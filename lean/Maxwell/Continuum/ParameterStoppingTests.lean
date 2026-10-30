import Maxwell.Continuum.ParameterStage

/-! Exact rational leakage and tail tests, and their derived binary
sufficient conditions. -/

namespace Maxwell.Continuum.Parameters

 theorem rationalDecay_absorbs {A : ℚ} {a t : ℕ} (hA : A ≤ (2 : ℚ)^a)
    (hat : a ≤ t/slowDivisor) : A*rationalDecay t ≤ 1 := by
  have hd : rationalDecay t ≤ (1/2 : ℚ)^a :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hat
  calc
    _ ≤ (2 : ℚ)^a*(1/2)^a := mul_le_mul hA hd (rationalDecay_pos t).le (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

 def LeakageTest (I : Input) (e k : ℕ) : Prop :=
  globalBudget e I.J I.m (boxCount (stageSpan I e k) (stageLength k) (stageBuffer I e k))
      (stageLength k) (stageSpacing I e k) I.K*rationalDecay (2^k) ≤
    errorBudget I.m (boxCount (stageSpan I e k) (stageLength k) (stageBuffer I e k))
      I.epsilon (stageTau I e k)/4

 def TailTest (I : Input) (e k : ℕ) : Prop :=
  (I.J : ℚ)*(2 : ℚ)^e*(stageLength k : ℚ)^5*rationalDecay (stageLength k) ≤
    (zeta (stageSpacing I e k))^2/4

 instance leakageTestDecidable (I : Input) (e k : ℕ) : Decidable (LeakageTest I e k) :=
  inferInstanceAs (Decidable (_ ≤ _))
 instance tailTestDecidable (I : Input) (e k : ℕ) : Decidable (TailTest I e k) :=
  inferInstanceAs (Decidable (_ ≤ _))

 theorem leakage_of_budget {I : Input} {e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ)
    (hf : stageBudgetExponent e p ℓ k (stageSpacing I e k) (stageBuffer I e k) ≤ 2^k/slowDivisor) :
    LeakageTest I e k := by
  exact stoppingRatio_test I.m_pos (boxCount_pos _ _ _) I.epsilon_pos (stageTau_pos I e k)
    (rationalDecay_absorbs (stageBudget_binary hI e k (stageBuffer I e k)) hf)

 theorem zeta_inverse_square (d : ℕ) : ((zeta d)^2)⁻¹ = (3 : ℚ)^(2*d) := by
  simp only [zeta, ← inv_pow]
  rw [show (1/3 : ℚ)⁻¹ = 3 by norm_num, ← pow_mul, Nat.mul_comm]

 theorem tail_ratio_binary {I : Input} {e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ) :
    4*(I.J : ℚ)*(2 : ℚ)^e*(stageLength k : ℚ)^5/(zeta (stageSpacing I e k))^2 ≤
      (2 : ℚ)^(2+p*ℓ+e+15*k+4*stageSpacing I e k) := by
  have hL := binary_pow (Nat.cast_nonneg (stageLength k)) (stageLength_binary k).le 5
  have hz : ((zeta (stageSpacing I e k))^2)⁻¹ ≤ (2 : ℚ)^(4*stageSpacing I e k) := by
    rw [zeta_inverse_square]
    calc
      _ ≤ (4 : ℚ)^(2*stageSpacing I e k) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by rw [show (4 : ℚ) = 2^2 by norm_num, ← pow_mul]; congr 1; omega
  have hp := binary_mul (binary_mul (binary_mul (binary_mul (show (4 : ℚ) ≤ (2 : ℚ)^2 by norm_num)
    hI.J (Nat.cast_nonneg I.J)) (le_refl ((2 : ℚ)^e)) (by positivity)) hL (by positivity))
      hz (by positivity)
  convert hp using 1
  · rw [div_eq_mul_inv]
  · congr 1; omega

 theorem tail_of_budget {I : Input} {e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ)
    (hf : stageBudgetExponent e p ℓ k (stageSpacing I e k) (stageBuffer I e k) ≤ 2^k/slowDivisor) :
    TailTest I e k := by
  have hexp : 2+p*ℓ+e+15*k+4*stageSpacing I e k ≤
      stageBudgetExponent e p ℓ k (stageSpacing I e k) (stageBuffer I e k) := by
    unfold stageBudgetExponent
    rw [Nat.mul_assoc 19 p ℓ]
    omega
  have hsize : (2 : ℕ)^k ≤ stageLength k := Nat.pow_le_pow_left (by decide) k
  have hh := rationalDecay_absorbs (tail_ratio_binary hI)
    (hexp.trans (hf.trans (Nat.div_le_div_right hsize)))
  have hz : 0 < (zeta (stageSpacing I e k))^2 := pow_pos (zeta_pos _) _
  have hx := (div_le_iff₀ hz).mp (show
      (4*(I.J : ℚ)*(2 : ℚ)^e*(stageLength k : ℚ)^5*rationalDecay (stageLength k))/
        (zeta (stageSpacing I e k))^2 ≤ 1 by simpa only [div_mul_eq_mul_div] using hh)
  change (I.J : ℚ)*(2 : ℚ)^e*(stageLength k : ℚ)^5*rationalDecay (stageLength k) ≤ _
  linarith

#print axioms leakage_of_budget
#print axioms tail_of_budget

end Maxwell.Continuum.Parameters
