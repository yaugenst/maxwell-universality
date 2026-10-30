import Maxwell.Continuum.FourierTensorWaveAxes
import Maxwell.Continuum.ChebyshevWaveProducerCost

/-! Polynomial cost of the reusable fixed wave-factor calls, including
the query, copies, and erasure of all large temporary words. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

theorem factor_monomial (a b c X : ℕ) :
    a*(b*X)*(c*X^4)^4=(a*b*c^4)*X^17 := by ring

def factorWorkspaceCoefficient : ℕ := 2^480*2^15*(2^137)^4+2^30+9

theorem factor_workspace_polynomial (Q N W : ℕ) :
    factorBankWidth Q N W+9 ≤ factorWorkspaceCoefficient*(Q+N+W+64)^17 ∧
      resetWidth Q N W+2 ≤ factorWorkspaceCoefficient*(Q+N+W+64)^17 := by
  let X := Q+N+W+64
  let P := waveWorkBits (8*Q) N
  let G := waveGrid (8*Q) N
  let D := waveDegree (8*Q) N
  let B := producerWidth Q N W
  have hX : 1 ≤ X := by dsimp [X];omega
  have hQ : Q ≤ X := by dsimp [X];omega
  have hD : D ≤ 2^8*X := by dsimp [D,waveDegree,X];omega
  have hP : P ≤ 2^9*X := by
    have hb := Machin.Runtime.nat_bits_le_self D
    change (waveDegree (8*Q) N).bits.length ≤ D at hb
    dsimp [P]
    rw [workBits_eq]
    omega
  have hG : G+1 ≤ 2^15*X := by
    change D+16*(8*Q+P+16)+1+1 ≤ _
    have hh : 64 ≤ X := by dsimp [X];omega
    omega
  have hd : dimensionWidth W ≤ 2^28*X := by
    unfold dimensionWidth
    exact Nat.mul_le_mul_left _ (by dsimp [X];omega)
  have hB : B ≤ 2^30*X := by
    have hW : W ≤ X := by dsimp [X]; omega
    change dimensionWidth W+P+W+8 ≤ _
    omega
  have hS : smallScale Q P B ≤ 2^34*X := by
    have hb := Machin.Runtime.nat_bits_le_self Q
    unfold smallScale
    have hh : 64 ≤ X := by dsimp [X];omega
    omega
  have hx4 : X ≤ X^4 := Nat.le_self_pow (by decide) X
  have hT : frequencyScale Q P B ≤ 2^137*X^4 := by
    have hs := Nat.pow_le_pow_left hS 4
    unfold frequencyScale
    nlinarith only [hs,hQ,hx4,Nat.zero_le (X^4)]
  have hreset : resetWidth Q N W+2 ≤ 2^30*X := by
    unfold resetWidth
    have hh : 64 ≤ X := by dsimp [X];omega
    omega
  have hbank : factorBankWidth Q N W+1 ≤ (2^480*2^15*(2^137)^4)*X^17 := calc
    _ ≤ runtimeBudget Q P B G := (actual_runtime_budget Q P B G).bank
    _ ≤ 2^480*(2^15*X)*(2^137*X^4)^4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) (Nat.pow_le_pow_left hT 4)
    _ = (2^480*2^15*(2^137)^4)*X^17 := factor_monomial _ _ _ _
  have hx17 : X ≤ X^17 := Nat.le_self_pow (by decide) X
  have hone : 1 ≤ X^17 := one_le_pow₀ hX
  refine ⟨?_,?_⟩
  · calc
      _ ≤ (2^480*2^15*(2^137)^4)*X^17+8 := Nat.add_le_add_right hbank 8
      _ ≤ (2^480*2^15*(2^137)^4)*X^17+(2^30+9)*X^17 := by
        exact Nat.add_le_add_left ((by decide : 8 ≤ 2^30+9).trans
          (Nat.le_mul_of_pos_right _ hone)) _
      _ = _ := by
        change (2^480*2^15*(2^137)^4)*X^17+(2^30+9)*X^17=factorWorkspaceCoefficient*X^17
        simp only [factorWorkspaceCoefficient,Nat.add_mul,Nat.add_assoc]

  have hc : 2^30 ≤ factorWorkspaceCoefficient := by
    unfold factorWorkspaceCoefficient
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  exact hreset.trans ((Nat.mul_le_mul_left _ hx17).trans (Nat.mul_le_mul_right _ hc))

#print axioms factor_workspace_polynomial


end Maxwell.Continuum.Profile.WaveMachine.Runtime
