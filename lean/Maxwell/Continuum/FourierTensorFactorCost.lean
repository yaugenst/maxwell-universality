import Maxwell.Continuum.FourierTensorFactorWorkspace

/-! Polynomial cost for the fixed reusable wave factor and three-axis call. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

def factorTimeCoefficient : ℕ := producerTimeCoefficient+2^110*factorWorkspaceCoefficient^2

theorem factorCost_polynomial (Q N W j : ℕ) (hj : j.bits.length ≤ W) :
    factorCost Q N W j ≤ factorTimeCoefficient*(Q+N+W+64)^240 := by
  let X := Q+N+W+64
  let Y := factorWorkspaceCoefficient*X^17
  let B := factorBankWidth Q N W
  have hX : 1 ≤ X := by dsimp [X];omega
  have hY : 1 ≤ Y := by
    dsimp [Y]
    have hc : 1 ≤ factorWorkspaceCoefficient := by
      unfold factorWorkspaceCoefficient
      exact (by decide : 1 ≤ 9).trans (Nat.le_add_left _ _)
    exact Nat.mul_le_mul hc (one_le_pow₀ hX)
  have hW : W ≤ Y := calc
    _ ≤ X := by dsimp [X];omega
    _ ≤ X^17 := Nat.le_self_pow (by decide) X
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by unfold factorWorkspaceCoefficient; exact (by decide : 1 ≤ 9).trans (Nat.le_add_left _ _))
  have hY2 : Y ≤ Y^2 := Nat.le_self_pow (by decide) Y
  have hone : 1 ≤ Y^2 := one_le_pow₀ hY
  have hb := factor_workspace_polynomial Q N W
  have hB : B+9 ≤ Y := hb.1
  have hR : resetWidth Q N W+2 ≤ Y := hb.2
  have hstage : RationalDataflow.stageCost B ≤ 2^96*Y^2 := by
    clear * -hB
    unfold RationalDataflow.stageCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hop : operationCost (B+1) ≤ 2^100*Y^2 := by
    clear * -hB
    unfold operationCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hreset : RationalDataflow.stageCost (resetWidth Q N W) ≤ 2^96*Y^2 := by
    unfold RationalDataflow.stageCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 2)
  have hread : cacheReadCost B ≤ 2^32*Y^2 := by
    clear * -hB hone
    have hsq := Nat.pow_le_pow_left (by omega : B+8 ≤ Y) 2
    change 2*(2^30*(B+8)^2)+1 ≤ _
    omega
  have hquery : cacheSelectCost B j ≤ 2^34*Y^2 := by
    have hj' := hj.trans (hW.trans hY2)
    clear * -hj' hread hone
    unfold cacheSelectCost
    omega
  have hextra : cacheSelectCost B j+factorFinishCost Q N W B ≤ 2^110*Y^2 := by
    clear * -hquery hstage hop hreset hone
    unfold factorFinishCost
    omega
  have hpoly : 2^110*Y^2 ≤ (2^110*factorWorkspaceCoefficient^2)*X^240 := calc
    _ = (2^110*factorWorkspaceCoefficient^2)*X^34 := by
      dsimp [Y]
      rw [mul_pow,←pow_mul]
      simp only [show 17*2=34 by decide,Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by decide))
  have hp := producerBound_polynomial Q N W
  change producerBound Q N W+(cacheSelectCost B j)+factorFinishCost Q N W B ≤ _
  calc
    _ = producerBound Q N W+(cacheSelectCost B j+factorFinishCost Q N W B) := Nat.add_assoc _ _ _
    _ ≤ producerTimeCoefficient*X^240+(2^110*factorWorkspaceCoefficient^2)*X^240 := by
      exact Nat.add_le_add hp (hextra.trans hpoly)
    _ = _ := by
      change producerTimeCoefficient*X^240+(2^110*factorWorkspaceCoefficient^2)*X^240=factorTimeCoefficient*X^240
      simp only [factorTimeCoefficient,Nat.add_mul]

#print axioms factorCost_polynomial

def axesTimeCoefficient : ℕ := 3*(factorTimeCoefficient+2^100)

theorem axesCost_polynomial (Q N W : ℕ) (j : Fin 3→ℕ) (hj : ∀i,(j i).bits.length ≤ W) :
    axesCost Q N W j ≤ axesTimeCoefficient*(Q+N+W+64)^240 := by
  let X := Q+N+W+64
  have hX : 1 ≤ X := by dsimp [X];omega
  have hW : W+2 ≤ X := by dsimp [X];omega
  have hx : X ≤ X^240 := Nat.le_self_pow (by decide) X
  have hone : 1 ≤ X^240 := one_le_pow₀ hX
  have hstage : RationalDataflow.stageCost W ≤ 2^96*X^240 := by
    unfold RationalDataflow.stageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hW 2).trans
      (Nat.pow_le_pow_right hX (by decide)))
  have hload : factorLoadCost W ≤ 2^100*X^240 := by
    have hw := (show W ≤ X by omega).trans hx
    unfold factorLoadCost
    omega
  have haxis (i : Fin 3) : axisCost Q N W (j i) ≤ (factorTimeCoefficient+2^100)*X^240 := by
    have hfactor := factorCost_polynomial Q N W (j i) (hj i)
    unfold axisCost
    calc
      _ ≤ 2^100*X^240+factorTimeCoefficient*X^240 := Nat.add_le_add hload hfactor
      _ = _ := by rw [Nat.add_mul,Nat.add_comm]
  unfold axesCost axesTimeCoefficient
  have h0 := haxis 0
  have h1 := haxis 1
  have h2 := haxis 2
  calc
    _ ≤ ((factorTimeCoefficient+2^100)*X^240)+(((factorTimeCoefficient+2^100)*X^240)+((factorTimeCoefficient+2^100)*X^240)) := Nat.add_le_add h0 (Nat.add_le_add h1 h2)
    _ = _ := by
      change ((factorTimeCoefficient+2^100)*X^240)+(((factorTimeCoefficient+2^100)*X^240)+((factorTimeCoefficient+2^100)*X^240))=(3*(factorTimeCoefficient+2^100))*X^240
      rw [Nat.mul_assoc]
      exact (by intro a; omega : ∀a : ℕ,a+(a+a)=3*a) _

#print axioms factorCost_polynomial
#print axioms axesCost_polynomial
end Maxwell.Continuum.Profile.WaveMachine.Runtime
