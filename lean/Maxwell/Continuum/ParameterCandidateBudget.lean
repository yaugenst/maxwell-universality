import Maxwell.Continuum.ParameterStage
import Maxwell.Continuum.ParameterCandidateSpacing

/-! Explicit integer bounds for every feedback budget at the octal outer
candidate. They imply a linear buffer and dominate the leakage exponent. -/

namespace Maxwell.Continuum.Parameters
set_option exponentiation.threshold 4096

 theorem candidate_exponent_le {M ℓ : ℕ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) :
    outerCandidateExponent M ℓ ≤ 17*M*ℓ := by
  have hu : Nat.clog 2 ℓ ≤ ℓ := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := ℓ)).le
  have hMl : M ≤ M*ℓ := Nat.le_mul_of_pos_right _ hℓ
  have hlM : ℓ ≤ M*ℓ := Nat.le_mul_of_pos_left _ (by omega)
  unfold outerCandidateExponent
  nlinarith

 theorem candidate_zero_budget {M e p ℓ d : ℕ} (hM : 4096 ≤ M) (he : e ≤ M)
    (hp : p ≤ M) (hℓ : 0 < ℓ) (hd : d ≤ 2^(9*M)*ℓ) :
    stageBudgetExponent e p ℓ (outerCandidateExponent M ℓ) d 0+1 ≤ 2^(10*M)*ℓ := by
  have hk := candidate_exponent_le (by omega : 1 ≤ M) hℓ
  have hMl : M ≤ M*ℓ := Nat.le_mul_of_pos_right _ hℓ
  have hpl := Nat.mul_le_mul_right ℓ hp
  have hpoly : 2236+32*e+393*outerCandidateExponent M ℓ+19*p*ℓ ≤ 10000*M*ℓ := by
    nlinarith
  have hcoeff : 10000*M ≤ (2 : ℕ)^(9*M) := by
    calc
      _ ≤ 2^14*2^M := Nat.mul_le_mul (by decide) (Nat.lt_two_pow_self (n := M)).le
      _ = 2^(14+M) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hbase := hpoly.trans (Nat.mul_le_mul_right ℓ hcoeff)
  have hsum : stageBudgetExponent e p ℓ (outerCandidateExponent M ℓ) d 0+1 ≤
      20*(2^(9*M)*ℓ) := by unfold stageBudgetExponent; omega
  calc
    _ ≤ 20*(2^(9*M)*ℓ) := hsum
    _ ≤ 32*(2^(9*M)*ℓ) := by omega
    _ = 2^(9*M+5)*ℓ := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))

 theorem stageSpacing_candidate {I : Input} {M e p ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ) :
    stageSpacing I e (outerCandidateExponent M ℓ) ≤ 2^(9*M)*ℓ :=
  selectedSpacing_candidate_bound hM he hp hℓ I.K_pos I.epsilon_pos hI.K (epsilon_lower_of_binary hI)

 theorem stageBuffer_candidate {I : Input} {M e p ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ) :
    stageBuffer I e (outerCandidateExponent M ℓ) ≤ 2^(11*M)*ℓ := by
  have hd := stageSpacing_candidate hI hM he hp hℓ
  have hb := candidate_zero_budget hM he hp hℓ hd
  have ht := (stageBuffer_upper hI e (outerCandidateExponent M ℓ)).le.trans
    (Nat.mul_le_mul_left (2^2049) hb)
  calc
    _ ≤ 2^2049*(2^(10*M)*ℓ) := ht
    _ = 2^(2049+10*M)*ℓ := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))

 theorem candidate_final_budget {M e p ℓ d t : ℕ} (hM : 4096 ≤ M) (he : e ≤ M)
    (hp : p ≤ M) (hℓ : 0 < ℓ) (hd : d ≤ 2^(9*M)*ℓ) (ht : t ≤ 2^(11*M)*ℓ) :
    stageBudgetExponent e p ℓ (outerCandidateExponent M ℓ) d t ≤ 2^(12*M)*ℓ := by
  have hb := candidate_zero_budget hM he hp hℓ hd
  have hpowers : 2^(10*M)*ℓ ≤ 2^(11*M)*ℓ :=
    Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))
  have hsum : stageBudgetExponent e p ℓ (outerCandidateExponent M ℓ) d t ≤
      10*(2^(11*M)*ℓ) := by unfold stageBudgetExponent at *; omega
  calc
    _ ≤ 10*(2^(11*M)*ℓ) := hsum
    _ ≤ 16*(2^(11*M)*ℓ) := by omega
    _ = 2^(11*M+4)*ℓ := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))

 theorem candidate_floor_covers {M ℓ : ℕ} (hM : 4096 ≤ M) :
    2^(12*M)*ℓ ≤ 2^outerCandidateExponent M ℓ/slowDivisor := by
  apply (Nat.le_div_iff_mul_le slowDivisor_pos).mpr
  have hℓ := Nat.le_pow_clog (by decide : 1 < 2) ℓ
  calc
    2^(12*M)*ℓ*slowDivisor = 2^(12*M+1024)*ℓ := by unfold slowDivisor; rw [pow_add]; ring
    _ ≤ 2^(15*M)*2^Nat.clog 2 ℓ :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) hℓ
    _ ≤ 2^(15*M)*2^(2*Nat.clog 2 ℓ) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := (pow_add _ _ _).symm

#print axioms stageBuffer_candidate
#print axioms candidate_final_budget
#print axioms candidate_floor_covers

end Maxwell.Continuum.Parameters
