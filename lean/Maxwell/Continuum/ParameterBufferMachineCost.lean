import Maxwell.Continuum.ParameterBufferMachineStart

/-! The executed buffer loop has cubic cost in its returned candidate and
incoming bit width. All coefficients depend only on the fixed program. -/
namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.SelectedParameters
set_option maxHeartbeats 1000000
attribute [local irreducible] formulas advance restartInstructions tests

def testCoefficient : ℕ := tests.length*(3000*8^4+8000+2)+2
def stepCoefficient : ℕ := 3000*8^advance.length+2^100+50+3000*8^formulas.length
def loopCoefficient : ℕ := 3000*8^formulas.length+stepCoefficient+2*testCoefficient+2
def widthCoefficient : ℕ := 1033*(2^formulas.length+1)
def costCoefficient : ℕ := loopCoefficient*widthCoefficient^2+3000*8^restartInstructions.length*1033^2

theorem testCost_bound (W : ℕ) : testCost W ≤ testCoefficient*(W+2)^2 := by
  have h : 1 ≤ (W+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_left (tests.length*2+2) h
  unfold testCost testCoefficient AllComparisons.unitCost
  nlinarith only [hm]

theorem inputWidth_le_width (N B : ℕ) : inputWidth N B ≤ width N B := by
  have h : 1 ≤ 2^formulas.length := Nat.one_le_pow _ _ (by decide)
  have hm := Nat.mul_le_mul_right (inputWidth N B+1) h
  unfold width
  omega

theorem initialCost_bound (N B : ℕ) :
    initialCost N B ≤ 3000*8^formulas.length*(width N B+2)^2 := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (inputWidth_le_width N B) 2) 2)

theorem powerCost_bound (T W : ℕ) (h : T ≤ W) : powerCost T W ≤ 50*(W+2)^2 := by
  have hm := Nat.mul_le_mul_right (13*W+25) (Nat.add_le_add_right h 1)
  unfold powerCost
  nlinarith only [hm]

theorem stepCost_bound (N B : ℕ) : stepCost N B ≤ stepCoefficient*(width N B+2)^2 := by
  have hT : 2^N ≤ width N B := (show 2^N ≤ inputWidth N B by unfold inputWidth;omega).trans
    (inputWidth_le_width N B)
  have h := powerCost_bound (2^N) (width N B) hT
  unfold stepCost stepCoefficient arithmeticCost
  nlinarith only [h]

theorem loop_cost (N B : ℕ) : costBound N B ≤ loopCoefficient*(N+1)*(width N B+2)^2 := by
  let Q := (width N B+2)^2
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hi := initialCost_bound N B
  have ht := testCost_bound (width N B)
  have hs := stepCost_bound N B
  change initialCost N B ≤ 3000*8^formulas.length*Q at hi
  change testCost (width N B) ≤ testCoefficient*Q at ht
  change stepCost N B ≤ stepCoefficient*Q at hs
  have hbody : stepCost N B+testCost (width N B)+1 ≤ (stepCoefficient+testCoefficient+1)*Q := by
    nlinarith only [ht,hs,hQ]
  have hhead : initialCost N B+testCost (width N B)+1 ≤ (3000*8^formulas.length+testCoefficient+1)*Q := by
    nlinarith only [hi,ht,hQ]
  have hhead' : initialCost N B+testCost (width N B)+1 ≤ loopCoefficient*Q :=
    hhead.trans (Nat.mul_le_mul_right Q (by unfold loopCoefficient;omega))
  have hbody' : stepCost N B+testCost (width N B)+1 ≤ loopCoefficient*Q :=
    hbody.trans (Nat.mul_le_mul_right Q (by unfold loopCoefficient;omega))
  calc
    costBound N B ≤ loopCoefficient*Q+N*(loopCoefficient*Q) :=
      Nat.add_le_add hhead' (Nat.mul_le_mul_left N hbody')
    _ = loopCoefficient*(N+1)*(width N B+2)^2 := by change _=loopCoefficient*(N+1)*Q;ring

theorem width_bound (N B : ℕ) : width N B+2 ≤ widthCoefficient*(2^N+B+1) := by
  have hd : 1 ≤ 2^N := Nat.one_le_pow _ _ (by decide)
  have hraw : inputWidth N B+1 ≤ 1033*(2^N+B+1) := by unfold inputWidth;omega
  have hm := Nat.mul_le_mul_left (2^formulas.length) hraw
  unfold width widthCoefficient
  nlinarith only [hm,hd,Nat.zero_le B]

theorem polynomial_cost (N B : ℕ) :
    resetCost B+costBound N B ≤ costCoefficient*(2^N+B+1)^3 := by
  let X := 2^N+B+1
  have hX : 1 ≤ X := Nat.succ_le_succ (Nat.zero_le _)
  have hN : N+1 ≤ X := by have := Nat.lt_two_pow_self (n:=N);unfold X;omega
  have hw := Nat.pow_le_pow_left (width_bound N B) 2
  have hl := loop_cost N B
  have hl' : costBound N B ≤ loopCoefficient*X*(widthCoefficient*X)^2 :=
    hl.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) hw)
  have hb : B+1033 ≤ 1033*X := by unfold X;have := Nat.one_le_pow N 2 (by decide);omega
  have hr := Nat.mul_le_mul_left (3000*8^restartInstructions.length) (Nat.pow_le_pow_left hb 2)
  have hsq : X^2 ≤ X^3 := Nat.pow_le_pow_right hX (by decide)
  have hr' := hr.trans (by
    calc
      3000*8^restartInstructions.length*(1033*X)^2 =
          (3000*8^restartInstructions.length*1033^2)*X^2 := by ring
      _ ≤ (3000*8^restartInstructions.length*1033^2)*X^3 := Nat.mul_le_mul_left _ hsq)
  change resetCost B ≤ _ at hr'
  change resetCost B+costBound N B ≤ costCoefficient*X^3
  calc
    _ ≤ (3000*8^restartInstructions.length*1033^2)*X^3+
        loopCoefficient*X*(widthCoefficient*X)^2 := Nat.add_le_add hr' hl'
    _ = costCoefficient*X^3 := by unfold costCoefficient;ring

#print axioms polynomial_cost
end Maxwell.Continuum.Parameters.BufferMachine
