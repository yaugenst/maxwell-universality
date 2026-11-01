import Maxwell.Continuum.ParameterSourcePrepare

/-! The fixed source-budget arithmetic and actual logarithm scan are
quadratic in the input word envelope. Their coefficients are source independent. -/
namespace Maxwell.Continuum.Parameters
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option exponentiation.threshold 1024

theorem SourceLogMachine.cost_quadratic (B : ℕ) : cost B≤2^26*(B+3)^2 := by
  have a : preparedWidth B+1≤16*(B+3):=by unfold preparedWidth;omega
  have b : preparedWidth B+2≤16*(B+3):=by unfold preparedWidth;omega
  have aa:=Nat.pow_le_pow_left a 2
  have bb:=Nat.pow_le_pow_left b 2
  have positive : 1≤(B+3)^2:=by nlinarith
  unfold cost
  nlinarith only [aa,bb,positive]

namespace SourcePrepare

def costCoefficient (κ η e : ℕ) : ℕ :=
  4*(3000*8^5)+
    3000*8^(SourceBudgetMachine.instructions κ η e).length*(SourceBudgetMachine.literalBound e+34)^2+
    2^26*(2^(SourceBudgetMachine.instructions κ η e).length*(SourceBudgetMachine.literalBound e+33)+3)^2

theorem cost_quadratic (κ η e n m circuit side sites : ℕ) :
    cost κ η e n m circuit side sites≤
      costCoefficient κ η e*(SourceInitialize.inputWidth n m circuit side sites+1)^2 := by
  let I:=SourceInitialize.inputWidth n m circuit side sites
  let L:=SourceBudgetMachine.literalBound e
  let a:=(SourceBudgetMachine.instructions κ η e).length
  let W:=budgetWidth κ η e n m circuit side sites
  have first : I+2≤2*(I+1):=by omega
  have second : 32*(I+1)+L+2≤(L+34)*(I+1):=by nlinarith
  have width : W+3≤(2^a*(L+33)+3)*(I+1):=by
    dsimp only [W,budgetWidth,SourceBudgetMachine.width,initialWidth]
    change 2^a*(32*(I+1)+L+1)+3≤_
    have h : 32*(I+1)+L+1≤(L+33)*(I+1):=by nlinarith
    have hh:=Nat.mul_le_mul_left (2^a) h
    nlinarith only [hh]
  have log:=(SourceLogMachine.cost_quadratic W).trans
    (Nat.mul_le_mul_left (2^26) (Nat.pow_le_pow_left width 2))
  have copy:=Nat.mul_le_mul_left (3000*8^5) (Nat.pow_le_pow_left first 2)
  have budget:=Nat.mul_le_mul_left (3000*8^a) (Nat.pow_le_pow_left second 2)
  unfold cost
  change 3000*8^5*(I+2)^2+(3000*8^a*(32*(I+1)+L+2)^2+SourceLogMachine.cost W)≤_
  calc
    _≤3000*8^5*(2*(I+1))^2+
        (3000*8^a*((L+34)*(I+1))^2+2^26*((2^a*(L+33)+3)*(I+1))^2):=by omega
    _=costCoefficient κ η e*(I+1)^2:=by unfold costCoefficient;dsimp only [a,L];ring

def widthCoefficient (κ η e : ℕ) : ℕ :=
  2^(SourceBudgetMachine.instructions κ η e).length*(SourceBudgetMachine.literalBound e+33)

theorem budgetWidth_linear (κ η e n m circuit side sites : ℕ) :
    budgetWidth κ η e n m circuit side sites≤
      widthCoefficient κ η e*(SourceInitialize.inputWidth n m circuit side sites+1) := by
  unfold budgetWidth SourceBudgetMachine.width widthCoefficient initialWidth
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

#print axioms cost_quadratic
#print axioms budgetWidth_linear
end SourcePrepare
end Maxwell.Continuum.Parameters
