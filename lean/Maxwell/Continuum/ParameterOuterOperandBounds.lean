import Maxwell.Continuum.ParameterOuterLoopCost
import Maxwell.Continuum.ParameterPrecision

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def sourceWidth (D : Data) : ℕ := D.constant.bits.length+D.sourceSize.bits.length+D.wells.bits.length+
  D.conditionNum.bits.length+D.conditionDen.bits.length+D.epsilonNum.bits.length+D.epsilonDen.bits.length+
  (D.span 0).bits.length+(D.span 1).bits.length+(D.span 2).bits.length

theorem sourceWidth_span (D : Data) (j : Fin 3) : (D.span j).bits.length ≤ sourceWidth D := by
  have h0 : (D.span 0).bits.length ≤ sourceWidth D := by unfold sourceWidth;omega
  have h1 : (D.span 1).bits.length ≤ sourceWidth D := by unfold sourceWidth;omega
  have h2 : (D.span 2).bits.length ≤ sourceWidth D := by unfold sourceWidth;omega
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem tauSteps_bound (D : Data) (hD : D.Positive) (e k : ℕ) :
    tauSteps D hD e k ≤ 25+12*k+4*stageSpacing (D.input hD) e k := by
  have ht := tauBits_le_binary (stageLength_pos k)
    (show stageLength k ≤ 2^(3*k) by exact_mod_cast (stageLength_binary k).le)
    (stageSpacing (D.input hD) e k)
  rw [tauBits,OuterTau.precision_eq _ _ (stageLength_pos k)] at ht
  change tauSteps D hD e k ≤ _ at ht
  omega

theorem baseWidth_bound (D : Data) (hD : D.Positive) (e k : ℕ) :
    baseWidth D hD e k ≤ 27+sourceWidth D+4*k+3*stageSpacing (D.input hD) e k := by
  have hl := Codec.power_bits_le 8 k
  have hz := Codec.power_bits_le 3 (stageSpacing (D.input hD) e k)
  have hd : (stageSpacing (D.input hD) e k).bits.length ≤ stageSpacing (D.input hD) e k := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have h8 : (8:ℕ).bits.length=4 := rfl
  have h3 : (3:ℕ).bits.length=2 := rfl
  rw [h8] at hl
  rw [h3] at hz
  change (stageLength k).bits.length ≤ _ at hl
  unfold baseWidth sourceWidth
  omega

theorem stageSpan_bits (D : Data) (hD : D.Positive) (e k : ℕ) (j : Fin 3) :
    (stageSpan (D.input hD) e k j).bits.length ≤ sourceWidth D+4*k+stageSpacing (D.input hD) e k+7 := by
  have hl := Codec.power_bits_le 8 k
  have hd : (stageSpacing (D.input hD) e k).bits.length ≤ stageSpacing (D.input hD) e k := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have h8 : (8:ℕ).bits.length=4 := rfl
  have h2 : (2:ℕ).bits.length=2 := rfl
  have h4 : (4:ℕ).bits.length=3 := rfl
  rw [h8] at hl
  change (stageLength k).bits.length ≤ _ at hl
  have hs := sourceWidth_span D j
  have h1 := RationalAccumulator.bits_mul_le 2 (stageLength k)
  have h2m := RationalAccumulator.bits_mul_le (2*stageLength k) (stageSpacing (D.input hD) e k)
  have h3m := RationalAccumulator.bits_mul_le (2*stageLength k*stageSpacing (D.input hD) e k) (D.span j)
  have ha := RationalAccumulator.bits_add_le (2*stageLength k*stageSpacing (D.input hD) e k*D.span j) 4
  rw [h2] at h1
  rw [h4] at ha
  change (2*stageLength k*stageSpacing (D.input hD) e k*D.span j+4).bits.length ≤ _
  omega

theorem bufferWidth_bound (D : Data) (hD : D.Positive) (e k : ℕ) :
    bufferWidth D hD e k ≤ 1200+4*sourceWidth D+40*k+20*stageSpacing (D.input hD) e k := by
  have hb := baseWidth_bound D hD e k
  have hl := Codec.power_bits_le 8 k
  have h8 : (8:ℕ).bits.length=4 := rfl
  rw [h8] at hl
  change (stageLength k).bits.length ≤ _ at hl
  have han := Codec.power_bits_le (stageLength k) 2
  have had := RationalAccumulator.bits_mul_le (2^1026) (8^(stageSpacing (D.input hD) e k))
  have hpow := Codec.power_bits_le 8 (stageSpacing (D.input hD) e k)
  rw [h8] at hpow
  have h1026 : (2^1026:ℕ).bits.length=1027 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  rw [h1026] at had
  have ht : (D.detuningDen hD e k).bits.length=tauSteps D hD e k+1 := by
    unfold Data.detuningDen tauSteps
    rw [Nat.size_eq_bits_len,Nat.size_pow]
  have htb := tauSteps_bound D hD e k
  have h0 := stageSpan_bits D hD e k 0
  have h1 := stageSpan_bits D hD e k 1
  have h2 := stageSpan_bits D hD e k 2
  unfold bufferWidth
  omega

#print axioms bufferWidth_bound
end Maxwell.Continuum.Parameters.OuterMachine
