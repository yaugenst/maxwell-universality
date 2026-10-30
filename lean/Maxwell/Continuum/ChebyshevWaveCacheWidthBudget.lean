import Maxwell.Continuum.ChebyshevWaveRuntimeWidthBudget
import Maxwell.Continuum.ChebyshevWaveCacheLoop

/-! A single proved word budget for every stage of the complete fixed
cache producer. The frequency and precision dependence remains explicit. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def runtimeBudget (Q P W grid : ℕ) : ℕ := 2^480*(grid+1)*(frequencyScale Q P W)^4

structure RuntimeWidthBudget (Q P W grid U : ℕ) : Prop where
  positive : 1 ≤ U
  q_le : Q ≤ U
  p_le : P ≤ U
  w_le : W ≤ U
  phase_le : Calibration.phaseBits Q (P+4) ≤ U
  summation : sumBankWidth Q P W grid ≤ U
  summand : productWorkWidth Q P (5*(W+1)) ≤ U
  sample : sampleWidth Q P (5*(W+1)) (sumBankWidth Q P W grid+5*(W+1)) 1 P ≤ U
  product : productWidth Q P (5*(W+1)) (sumBankWidth Q P W grid+5*(W+1)) ≤ U
  coefficient : coefficientWidth Q P grid W ≤ U
  cosine : 256*(coefficientWidth Q P grid W+1) ≤ U
  encoded : encodedWidth Q P grid W ≤ U
  bank : cacheBankWidth Q P grid W+1 ≤ U

theorem actual_runtime_budget (Q P W grid : ℕ) :
    RuntimeWidthBudget Q P W grid (runtimeBudget Q P W grid) := by
  let T := frequencyScale Q P W
  let R := (grid+1)*T^4
  have hT := frequencyScale_bounds Q P W
  have hS := smallScale_bounds Q P W
  have hT4 : T ≤ T^4 := Nat.le_self_pow (by decide) T
  have hR4 : T^4 ≤ R := by dsimp [R];nlinarith only [Nat.zero_le grid,Nat.zero_le (T^4)]
  have hR : 1 ≤ R := (hT.1.trans hT4).trans hR4
  have hQ : Q ≤ R := hT.2.1.trans (hT4.trans hR4)
  have hP : P ≤ R := hS.2.1.trans (hT.2.2.1.trans (hT4.trans hR4))
  have hW : W ≤ R := hS.2.2.1.trans (hT.2.2.1.trans (hT4.trans hR4))
  have hW5 : 5*(W+1) ≤ R := hS.2.2.2.1.trans (hT.2.2.1.trans (hT4.trans hR4))
  have hPhase : Calibration.phaseBits Q (P+4) ≤ R :=
    hS.2.2.2.2.trans (hT.2.2.1.trans (hT4.trans hR4))
  have hSum : sumBankWidth Q P W grid ≤ 2^440*R := by
    simpa only [R,T,Nat.mul_assoc] using sum_width_budget Q P W grid
  have hActual := actual_width_budget Q P W
  have hSample : WaveMachine.workWidth Q P (5*(W+1)) ≤ 2^424*R :=
    hActual.1.trans (Nat.mul_le_mul_left _ hR4)
  have hProduct : productInputWidth Q P (5*(W+1)) ≤ 2^428*R :=
    hActual.2.1.trans (Nat.mul_le_mul_left _ hR4)
  have hSummand : productWorkWidth Q P (5*(W+1)) ≤ 2^436*R :=
    hActual.2.2.trans (Nat.mul_le_mul_left _ hR4)
  have hPbits : P.bits.length ≤ R := (Machin.Runtime.nat_bits_le_self P).trans hP
  have hCoeff : coefficientWidth Q P grid W ≤ 2^446*R := by
    unfold coefficientWidth
    omega
  have hCos : 256*(coefficientWidth Q P grid W+1) ≤ 2^456*R := by omega
  have hEncoded : encodedWidth Q P grid W ≤ 2^458*R := by unfold encodedWidth;omega
  have hBank : cacheBankWidth Q P grid W+1 ≤ 2^460*R := by unfold cacheBankWidth;omega
  have hU : runtimeBudget Q P W grid=2^480*R := by simp only [runtimeBudget,R,T,Nat.mul_assoc]
  rw [hU]
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_,?_,by omega,by omega,
    by omega,by omega⟩
  · unfold sampleWidth
    norm_num only [show (1:ℕ).bits.length=1 by decide]
    omega
  · unfold productWidth
    omega

#print axioms actual_runtime_budget
end Maxwell.Continuum.Profile.WaveMachine.Runtime
