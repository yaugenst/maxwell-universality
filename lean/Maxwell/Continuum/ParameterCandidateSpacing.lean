import Maxwell.Continuum.ParameterSpacingSearch

/-! An explicit octal candidate with sixth-power input-log size, and a
linear-in-input-log bound on the actual spacing search at that candidate. -/

namespace Maxwell.Continuum.Parameters

 def outerCandidateExponent (M ℓ : ℕ) : ℕ := 15*M+2*Nat.clog 2 ℓ
 def outerCandidate (M ℓ : ℕ) : ℕ := 8^outerCandidateExponent M ℓ

 theorem outerCandidate_lower (M ℓ : ℕ) : ℓ^6 ≤ outerCandidate M ℓ := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) ℓ) 6
  have he : (2^Nat.clog 2 ℓ)^6 = 8^(2*Nat.clog 2 ℓ) := by
    rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [he] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) (by unfold outerCandidateExponent; omega))

 theorem outerCandidate_upper {M ℓ : ℕ} (hℓ : 0 < ℓ) :
    outerCandidate M ℓ < 64*8^(15*M)*ℓ^6 := by
  have hp := powerCeiling_upper (by decide : 1 < 2) hℓ
  have hh := Nat.pow_lt_pow_left hp (by decide : (6 : ℕ) ≠ 0)
  have he : outerCandidate M ℓ = 8^(15*M)*(powerCeiling 2 ℓ)^6 := by
    unfold outerCandidate outerCandidateExponent powerCeiling
    rw [pow_add]
    congr 1
    rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [he]
  have hm := Nat.mul_lt_mul_of_pos_left hh (by positivity : 0 < (8 : ℕ)^(15*M))
  convert hm using 1
  ring

 theorem spacingThreshold_candidate_bound {M e p ℓ : ℕ} (hM : 4096 ≤ M)
    (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ) :
    2*spacingThreshold e (3*outerCandidateExponent M ℓ) (p*ℓ) (p*ℓ) ≤
      2^(9*M)*ℓ := by
  let u := Nat.clog 2 ℓ
  have hu : u ≤ ℓ := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := ℓ)).le
  have hpowu : 2^u ≤ 2*ℓ := (powerCeiling_upper (by decide : 1 < 2) hℓ).le
  have hs : (2^e)^8 ≤ 2^(8*M)*ℓ := by
    rw [← pow_mul]
    have hh : (2 : ℕ)^(e*8) ≤ 2^(8*M) := Nat.pow_le_pow_right (by decide) (by omega)
    exact hh.trans (Nat.le_mul_of_pos_right _ hℓ)
  have hroot : 2^((4*e+3*outerCandidateExponent M ℓ+14)/15) ≤ 2^(8*M)*ℓ := by
    have hexp : (4*e+3*outerCandidateExponent M ℓ+14)/15 ≤ 7*M+u+1 := by
      unfold outerCandidateExponent
      change (4*e+3*(15*M+2*u)+14)/15 ≤ _
      omega
    calc
      _ ≤ 2^(7*M+u+1) := Nat.pow_le_pow_right (by decide) hexp
      _ = 2^(7*M+1)*2^u := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^(7*M+1)*(2*ℓ) := Nat.mul_le_mul_left _ hpowu
      _ = 2^(7*M+2)*ℓ := by rw [show 7*M+2 = (7*M+1)+1 by omega, pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))
  have hlin : 8*(1050+4*e+12*(3*outerCandidateExponent M ℓ)+p*ℓ+p*ℓ+2) ≤
      4952*M*ℓ := by
    unfold outerCandidateExponent
    change 8*(1050+4*e+12*(3*(15*M+2*u))+p*ℓ+p*ℓ+2) ≤ _
    have hMℓ : M ≤ M*ℓ := Nat.le_mul_of_pos_right _ hℓ
    have hℓM : ℓ ≤ M*ℓ := Nat.le_mul_of_pos_left _ (by omega)
    have hpℓ := Nat.mul_le_mul_right ℓ hp
    nlinarith
  have hcoeff : 4952*M ≤ (2 : ℕ)^(8*M) := by
    calc
      _ ≤ 2^13*2^M := Nat.mul_le_mul (by decide) (Nat.lt_two_pow_self (n := M)).le
      _ = 2^(13+M) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hthird := hlin.trans (Nat.mul_le_mul_right ℓ hcoeff)
  have hsum : spacingThreshold e (3*outerCandidateExponent M ℓ) (p*ℓ) (p*ℓ) ≤
      3*(2^(8*M)*ℓ) := by unfold spacingThreshold; omega
  calc
    _ ≤ 2*(3*(2^(8*M)*ℓ)) := Nat.mul_le_mul_left _ hsum
    _ ≤ 8*(2^(8*M)*ℓ) := by omega
    _ = 2^(8*M+3)*ℓ := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))

 theorem selectedSpacing_candidate_bound {M e p ℓ : ℕ} {K ε : ℚ} (hM : 4096 ≤ M)
    (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ) (hK : 0 < K) (hε : 0 < ε)
    (hKb : K ≤ (2 : ℚ)^(p*ℓ)) (hεb : (1/2 : ℚ)^(p*ℓ) ≤ ε) :
    selectedSpacing e (outerCandidate M ℓ) K ε hK hε ≤ 2^(9*M)*ℓ := by
  have hL : outerCandidate M ℓ ≤ 2^(3*outerCandidateExponent M ℓ) := by
    unfold outerCandidate
    rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul]
  exact (selectedSpacing_lt_threshold hK hε hL hKb hεb).le.trans
    (spacingThreshold_candidate_bound hM he hp hℓ)

#print axioms spacingThreshold_candidate_bound
#print axioms selectedSpacing_candidate_bound

end Maxwell.Continuum.Parameters
