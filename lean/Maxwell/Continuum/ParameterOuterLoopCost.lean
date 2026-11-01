import Maxwell.Continuum.ParameterOuterStageCost

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def advanceCoefficient : ℕ := 3000*8^advance.length
def loopCoefficient : ℕ := advanceCoefficient+2*stageCoefficient+2

theorem loop_count_le_width (D : Data) (hD : D.Positive) (e base ℓ B : ℕ) (hℓ : 0<ℓ) :
    selectedOuterSteps (D.input hD) e base ℓ hℓ+1 ≤ loopWidth D hD e base ℓ B hℓ := by
  have hw := loopWidth_stage D hD e base ℓ B hℓ (selectedOuterSteps (D.input hD) e base ℓ hℓ) le_rfl
  have hn := Nat.lt_two_pow_self (n:=initialExponent base ℓ+selectedOuterSteps (D.input hD) e base ℓ hℓ)
  dsimp only [stageWidth] at hw
  omega

theorem loop_cost_bound (D : Data) (hD : D.Positive) (e base ℓ B : ℕ) (hℓ : 0<ℓ) :
    let W := loopWidth D hD e base ℓ B hℓ
    loopCost D hD e base ℓ W hℓ ≤ loopCoefficient*(W+1033)^5 := by
  dsimp only
  let W := loopWidth D hD e base ℓ B hℓ
  let N := selectedOuterSteps (D.input hD) e base ℓ hℓ
  let X := W+1033
  have hX : 1 ≤ X := by unfold X;omega
  have hN : N+1 ≤ W := loop_count_le_width D hD e base ℓ B hℓ
  have sum : loopTestCost D hD e base ℓ W hℓ ≤ (N+1)*(stageCoefficient*X^3) := by
    calc
      _ ≤ ∑n∈Finset.range (N+1),stageCoefficient*X^3 := by
        apply Finset.sum_le_sum
        intro n hn
        exact stage_cost_bound D hD e (initialExponent base ℓ+n) W
          (loopWidth_stage D hD e base ℓ B hℓ n (by have := Finset.mem_range.mp hn;omega))
      _ = _ := by simp
  have test : loopTestCost D hD e base ℓ W hℓ ≤ stageCoefficient*X^4 := by
    calc
      _ ≤ X*(stageCoefficient*X^3) := sum.trans (Nat.mul_le_mul_right _ (by unfold X;omega))
      _ = _ := by ring
  have adv : advanceCost W ≤ advanceCoefficient*X^4 := by
    unfold advanceCost advanceCoefficient
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by unfold X;omega) 2).trans (Nat.pow_le_pow_right hX (by decide))
  have one4 : 1 ≤ X^4 := Nat.one_le_pow _ _ hX
  have body : advanceCost W+loopTestCost D hD e base ℓ W hℓ+1 ≤
      (advanceCoefficient+stageCoefficient+1)*X^4 := by nlinarith only [adv,test,one4]
  have head : loopTestCost D hD e base ℓ W hℓ+1 ≤ (stageCoefficient+1)*X^4 := by
    nlinarith only [test,one4]
  change loopCost D hD e base ℓ W hℓ ≤ loopCoefficient*X^5
  calc
    _ ≤ (stageCoefficient+1)*X^4+X*((advanceCoefficient+stageCoefficient+1)*X^4) :=
      Nat.add_le_add head (Nat.mul_le_mul (by unfold X;omega) body)
    _ ≤ (stageCoefficient+1)*X^5+X*((advanceCoefficient+stageCoefficient+1)*X^4) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by decide))) _
    _ = _ := by unfold loopCoefficient;ring

#print axioms loop_cost_bound
end Maxwell.Continuum.Parameters.OuterMachine
