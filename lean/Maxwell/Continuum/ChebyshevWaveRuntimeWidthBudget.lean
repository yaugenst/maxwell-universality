import Maxwell.Continuum.ChebyshevWaveRuntimeSumStep

/-! Separate budgets for frequency size and requested precision. Keeping
the logarithmic inner phase precision separate avoids multiplying degree
exponents through the nested phase evaluation. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def smallScale (Q P W : ℕ) : ℕ := 8*(P+W+Q.bits.length+32)
def frequencyScale (Q P W : ℕ) : ℕ := Q+(smallScale Q P W)^4

theorem smallScale_bounds (Q P W : ℕ) :
    1 ≤ smallScale Q P W ∧ P ≤ smallScale Q P W ∧ W ≤ smallScale Q P W ∧
      5*(W+1) ≤ smallScale Q P W ∧ Calibration.phaseBits Q (P+4) ≤ smallScale Q P W := by
  rw [Calibration.phaseBits,PhaseMachine.Runtime.clog_two_succ]
  unfold smallScale
  omega

theorem frequencyScale_bounds (Q P W : ℕ) :
    1 ≤ frequencyScale Q P W ∧ Q ≤ frequencyScale Q P W ∧
      smallScale Q P W ≤ frequencyScale Q P W ∧
      (smallScale Q P W)^4 ≤ frequencyScale Q P W := by
  have hs := (smallScale_bounds Q P W).1
  have hpow := Nat.le_self_pow (by decide : 4≠0) (smallScale Q P W)
  unfold frequencyScale
  omega

theorem sampler_width_budget (Q P W S T : ℕ)
    (hS : 1 ≤ S) (hW : W ≤ S) (hP : P ≤ S) (hphase : Calibration.phaseBits Q (P+4) ≤ S)
    (hQ : Q ≤ T) (hS4 : S^4 ≤ T) :
    WaveMachine.workWidth Q P W ≤ 2^424*T^4 ∧
      productInputWidth Q P W ≤ 2^428*T^4 ∧ productWorkWidth Q P W ≤ 2^436*T^4 := by
  have hST : S ≤ T := (Nat.le_self_pow (by decide : 4≠0) S).trans hS4
  have hT : 1 ≤ T := hS.trans hST
  have hT4 : T ≤ T^4 := Nat.le_self_pow (by decide : 4≠0) T
  have hone : 1 ≤ T^4 := one_le_pow₀ hT
  have hin : innerWidth Q P W ≤ 2^84*T := by
    calc
      _ ≤ 2^68*(15*S)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ ≤ 2^84*S^4 := by
        rw [Nat.mul_pow,←Nat.mul_assoc]
        exact Nat.mul_le_mul_right (S^4) (by norm_num : 2^68*15^4 ≤ (2:ℕ)^84)
      _ ≤ _ := Nat.mul_le_mul_left _ hS4
  have harg : argumentWidth Q P W ≤ 2^86*T := by
    unfold argumentWidth
    omega
  have hout : outerWidth Q P W ≤ 2^420*T^4 := by
    calc
      _ ≤ 2^68*(2^88*T)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = _ := by ring
  have hwork : WaveMachine.workWidth Q P W ≤ 2^424*T^4 := by
    have hin4 := hin.trans (Nat.mul_le_mul_left (2^84) hT4)
    have harg4 := harg.trans (Nat.mul_le_mul_left (2^86) hT4)
    unfold WaveMachine.workWidth
    omega
  have hchar : characterWidth P W ≤ 2^88*T^4 := by
    calc
      _ ≤ 2^68*(32*S)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = 2^88*S^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hS4.trans hT4)
  have hp : productInputWidth Q P W ≤ 2^428*T^4 := by
    unfold productInputWidth
    omega
  refine ⟨hwork,hp,?_⟩
  unfold productWorkWidth
  omega

theorem actual_width_budget (Q P W : ℕ) :
    WaveMachine.workWidth Q P (5*(W+1)) ≤ 2^424*(frequencyScale Q P W)^4 ∧
      productInputWidth Q P (5*(W+1)) ≤ 2^428*(frequencyScale Q P W)^4 ∧
      productWorkWidth Q P (5*(W+1)) ≤ 2^436*(frequencyScale Q P W)^4 := by
  have hs := smallScale_bounds Q P W
  have ht := frequencyScale_bounds Q P W
  exact sampler_width_budget Q P (5*(W+1)) _ _ hs.1 hs.2.2.2.1 hs.2.1 hs.2.2.2.2 ht.2.1 ht.2.2.2

theorem sum_width_budget (Q P W grid : ℕ) :
    sumBankWidth Q P W grid ≤ 2^440*(grid+1)*(frequencyScale Q P W)^4 := by
  have hs := smallScale_bounds Q P W
  have ht := frequencyScale_bounds Q P W
  have h1 : 1 ≤ (frequencyScale Q P W)^4 := one_le_pow₀ ht.1
  have hw := hs.2.2.1.trans (ht.2.2.1.trans (Nat.le_self_pow (by decide : 4≠0) _))
  have hp := (actual_width_budget Q P W).2.2
  unfold sumBankWidth
  nlinarith only [Nat.mul_le_mul_left (grid+1) hp,hw,h1,Nat.zero_le grid]

#print axioms actual_width_budget
#print axioms sum_width_budget
end Maxwell.Continuum.Profile.WaveMachine.Runtime
