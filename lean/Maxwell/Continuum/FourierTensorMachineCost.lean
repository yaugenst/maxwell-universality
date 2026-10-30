import Maxwell.Continuum.FourierTensorMachineFold

/-! Uniform polynomial bit cost for a complete tensor contraction. -/
namespace Maxwell.Continuum.Profile.TensorMachine
open RationalDataflow PartArray
set_option maxHeartbeats 2500000

theorem coefficientCost_polynomial (n W wordLength : ℕ) :
    coefficientCost n W wordLength≤2^120*(n+1)^3*(W+1)^2+(n+1)*(13*wordLength+15) := by
  have hw : accumulatorWidth n W+12≤34*(n+1)*(W+1) := by
    unfold accumulatorWidth
    nlinarith
  have hw2 : accumulatorWidth n W+2≤34*(n+1)*(W+1) := by omega
  have hw3 : accumulatorWidth n W+3≤34*(n+1)*(W+1) := by omega
  have hs := Nat.pow_le_pow_left hw2 2
  have ho := Nat.pow_le_pow_left hw3 2
  have hr := Nat.pow_le_pow_left hw 2
  have hpos : 1≤(n+1)^2*(W+1)^2 := Nat.succ_le_of_lt (by positivity)
  have hstage : stageCost (accumulatorWidth n W)≤2^107*(n+1)^2*(W+1)^2 := by
    unfold stageCost
    nlinarith only [hs]
  have hbody : rowFoldStepCost 8 3 (accumulatorWidth n W) readPlan body≤
      2^116*(n+1)^2*(W+1)^2 := by
    simp only [rowFoldStepCost,rowPlanCost,readPlan,List.length_cons,List.length_nil,body_steps]
    norm_num only [Nat.reduceAdd,Nat.reducePow,Nat.reduceMul]
    change 8*(2^30*(accumulatorWidth n W+12)^2)+1+
      16*operationCost (accumulatorWidth n W)+1≤_
    unfold operationCost
    nlinarith only [ho,hr,hpos]
  have hm := Nat.mul_le_mul_left n hbody
  unfold coefficientCost
  nlinarith only [hstage,hm,Nat.zero_le ((n+1)^2*(W+1)^2)]

theorem coefficientCost_uniform (n W wordLength : ℕ) (hlen : wordLength≤W) :
    coefficientCost n W wordLength≤2^121*(n+1)^3*(W+1)^2 := by
  have h := coefficientCost_polynomial n W wordLength
  have hp : W+1≤(W+1)^2 := le_self_pow₀ (by omega) (by decide)
  have hn : n+1≤(n+1)^3 := le_self_pow₀ (by omega) (by decide)
  have htail : (n+1)*(13*wordLength+15)≤15*(n+1)^3*(W+1)^2 := by
    calc
      _ ≤ (n+1)*(15*(W+1)) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (n+1)^3*(15*((W+1)^2)) := Nat.mul_le_mul hn (Nat.mul_le_mul_left _ hp)
      _ = _ := by ring
  nlinarith only [h,htail,Nat.zero_le ((n+1)^3*(W+1)^2)]

#print axioms coefficientCost_polynomial
#print axioms coefficientCost_uniform
end Maxwell.Continuum.Profile.TensorMachine
