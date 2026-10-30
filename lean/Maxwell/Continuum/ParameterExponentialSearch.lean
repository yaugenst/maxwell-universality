import Maxwell.Continuum.ParameterPowerSearch
import Maxwell.Continuum.ParameterDyadic

/-! Exact absorption of cubic-box feedback. The ninth power comes from
NΩ (1+NΩ)², with each count cubic in the buffer length. -/

namespace Maxwell.Continuum.Parameters

set_option exponentiation.threshold 4096

def bufferCandidateExponent (a : ℕ) : ℕ := 2048+Nat.clog 2 (a+1)
def bufferCandidate (a : ℕ) : ℕ := 2^bufferCandidateExponent a

theorem bufferCandidate_floor (a : ℕ) :
    bufferCandidate a/slowDivisor = 2^(1024+Nat.clog 2 (a+1)) := by
  unfold bufferCandidate bufferCandidateExponent slowDivisor
  rw [show 2048+Nat.clog 2 (a+1) = 1024+(1024+Nat.clog 2 (a+1)) by omega,
    pow_add, Nat.mul_div_right _ (by positivity : 0 < 2^1024)]

theorem bufferCandidate_exponent_budget (a : ℕ) :
    a+9*(bufferCandidateExponent a+1) ≤ bufferCandidate a/slowDivisor := by
  have hu : Nat.clog 2 (a+1) ≤ a+1 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := a+1)).le
  have hl := Nat.le_pow_clog (by decide : 1 < 2) (a+1)
  rw [bufferCandidate_floor, pow_add]
  unfold bufferCandidateExponent
  have hc : 18460 ≤ (2 : ℕ)^1024 := by norm_num
  have hm := Nat.mul_le_mul_right (2^Nat.clog 2 (a+1)) hc
  nlinarith

/-- Rational comparison, including the complete polynomial feedback. -/
theorem bufferCandidate_passes {A : ℚ} {a : ℕ} (hAb : A ≤ (2 : ℚ)^a) :
    A*(1+(bufferCandidate a : ℚ))^9*rationalDecay (bufferCandidate a) ≤ 1 := by
  have ht : (1 : ℚ) ≤ (bufferCandidate a : ℚ) := by
    exact_mod_cast (show 1 ≤ bufferCandidate a from one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))
  have htcast : (bufferCandidate a : ℚ) = (2 : ℚ)^bufferCandidateExponent a := by
    simp only [bufferCandidate, Nat.cast_pow, Nat.cast_ofNat]
  have hs : 1+(bufferCandidate a : ℚ) ≤ (2 : ℚ)^(bufferCandidateExponent a+1) := by
    rw [pow_succ, ← htcast]
    linarith
  have hp : A*(1+(bufferCandidate a : ℚ))^9 ≤
      (2 : ℚ)^(a+9*(bufferCandidateExponent a+1)) := by
    calc
      _ ≤ (2 : ℚ)^a*((2 : ℚ)^(bufferCandidateExponent a+1))^9 :=
        mul_le_mul hAb (pow_le_pow_left₀ (by positivity) hs 9) (by positivity) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hd : rationalDecay (bufferCandidate a) ≤
      (1/2 : ℚ)^(a+9*(bufferCandidateExponent a+1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (bufferCandidate_exponent_budget a)
  calc
    _ ≤ (2 : ℚ)^(a+9*(bufferCandidateExponent a+1))*
        (1/2)^(a+9*(bufferCandidateExponent a+1)) :=
      mul_le_mul hp hd (rationalDecay_pos _).le (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

theorem bufferCandidate_upper (a : ℕ) : bufferCandidate a < 2^2049*(a+1) := by
  have hp := powerCeiling_upper (by decide : 1 < 2) (Nat.zero_lt_succ a)
  have hm := Nat.mul_lt_mul_of_pos_left hp (by positivity : 0 < (2 : ℕ)^2048)
  calc
    bufferCandidate a = 2^2048*powerCeiling 2 (a+1) := by
      simp only [bufferCandidate, bufferCandidateExponent, pow_add, powerCeiling]
    _ < 2^2048*(2*(a+1)) := hm
    _ = 2^2049*(a+1) := by
      have he : (2 : ℕ)^2049 = 2^2048*2 := by norm_num
      rw [he]
      ac_rfl

theorem bufferCandidate_bits (a : ℕ) :
    (bufferCandidate a).bits.length = 2049+Nat.clog 2 (a+1) := by
  rw [Nat.size_eq_bits_len, bufferCandidate, Nat.size_pow, bufferCandidateExponent]
  omega

#print axioms bufferCandidate_passes
#print axioms bufferCandidate_upper

end Maxwell.Continuum.Parameters
