import Maxwell.Continuum.ParameterOuterMachine

/-! Polynomial charged cost of an executed stage in its uniform word
width. Constants depend only on the fixed instruction lists. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
attribute [local irreducible] SpacingMachine.formulas BufferMachine.formulas
attribute [local irreducible] loadSpacing saveSpacing prepareTau prepareSpans loadBuffer saveBuffer tailPrepare

def spacingCoefficient : ℕ := 3000*8^loadSpacing.length+3000*8^SpacingMachine.resetInstructions.length+
  SpacingMachine.loopCoefficient+3000*8^saveSpacing.length
def tauCoefficient : ℕ := 3000*8^prepareTau.length+128*GeometricAdapter.costCoefficient+50
def bufferCoefficient : ℕ := 3000*8^prepareSpans.length+3000*8^loadBuffer.length+
  3000*8^BufferMachine.restartInstructions.length+BufferMachine.loopCoefficient+3000*8^saveBuffer.length
def stoppingCoefficient : ℕ := 2*(3000*8^7+2^100+50)+3000*8^tailPrepare.length+
  tests.length*(3000*8^4+8000+2)+2
def stageCoefficient : ℕ := spacingCoefficient+tauCoefficient+bufferCoefficient+stoppingCoefficient

theorem square_le_cube (W c : ℕ) (hc : c ≤ 1033) : (W+c)^2 ≤ (W+1033)^3 :=
  (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))

theorem spacing_cost_bound (D : Data) (hD : D.Positive) (e k W B : ℕ)
    (hw : SpacingMachine.width (spacingSteps D hD e k) B ≤ W) :
    spacingCost D hD e k W B ≤ spacingCoefficient*(W+1033)^3 := by
  let N := spacingSteps D hD e k
  change SpacingMachine.width N B ≤ W at hw
  have hn : N+1 ≤ SpacingMachine.width N B := by
    have h := Nat.lt_two_pow_self (n:=N)
    have hmul := Nat.le_mul_of_pos_left (SpacingMachine.inputWidth N B+1)
      (Nat.two_pow_pos SpacingMachine.formulas.length)
    change SpacingMachine.inputWidth N B+1 ≤ SpacingMachine.width N B at hmul
    dsimp only [SpacingMachine.inputWidth] at hmul
    omega
  have hcost := SpacingMachine.loop_cost N B
  have hmain : SpacingMachine.costBound N B ≤ SpacingMachine.loopCoefficient*(W+1033)^3 := by
    calc
      _ ≤ SpacingMachine.loopCoefficient*(W+1033)*(W+1033)^2 := hcost.trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) 2))
      _ = _ := by ring
  have ha := Nat.mul_le_mul_left (3000*8^loadSpacing.length) (square_le_cube W 2 (by decide))
  have hr := Nat.mul_le_mul_left (3000*8^SpacingMachine.resetInstructions.length) (square_le_cube W 1032 (by decide))
  have hz := Nat.mul_le_mul_left (3000*8^saveSpacing.length) (square_le_cube W 2 (by decide))
  unfold spacingCost spacingCoefficient SpacingMachine.resetCost
  dsimp only [N] at hmain
  nlinarith only [ha,hr,hmain,hz]

theorem tau_cost_bound (D : Data) (hD : D.Positive) (e k W B : ℕ)
    (hp : tauInputWidth B ≤ W) (hw : OuterTau.width (tauSteps D hD e k) (tauInputWidth B) ≤ W) :
    tauStageCost D hD e k W B ≤ tauCoefficient*(W+1033)^3 := by
  let N := tauSteps D hD e k
  have hn : N+1 ≤ W := (le_max_right _ _).trans hw
  have hgeo := GeometricAdapter.costBound_polynomial N 2 (tauInputWidth B)
  have hg : GeometricAdapter.costBound N 2 (tauInputWidth B) ≤
      (128*GeometricAdapter.costCoefficient)*(W+1033)^3 := by
    calc
      _ ≤ GeometricAdapter.costCoefficient*(2+2)^2*(2*(W+1033))^3 := hgeo.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
      _ = _ := by ring
  have hb : N.bits.length ≤ N := by rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have hpower : (N+1)*(13*N.bits.length+25)+21*N.bits.length+27 ≤ 50*(W+2)^2 := by
    have h1 := Nat.mul_le_mul (by omega : N+1 ≤ W+1) (by omega : 13*N.bits.length+25 ≤ 13*W+25)
    nlinarith only [h1,hb,hn]
  have hpower' := hpower.trans (Nat.mul_le_mul_left 50 (square_le_cube W 2 (by decide)))
  have ha := Nat.mul_le_mul_left (3000*8^prepareTau.length) (square_le_cube W 2 (by decide))
  unfold tauStageCost tauCoefficient OuterTau.costBound
  dsimp only [N] at hg hpower'
  nlinarith only [hg,hpower',ha]

theorem buffer_cost_bound (D : Data) (hD : D.Positive) (e k W B : ℕ)
    (hw : BufferMachine.width (bufferSteps D hD e k) B ≤ W) :
    bufferStageCost D hD e k W B ≤ bufferCoefficient*(W+1033)^3 := by
  let N := bufferSteps D hD e k
  change BufferMachine.width N B ≤ W at hw
  have hn : N+1 ≤ BufferMachine.width N B := by
    have h := Nat.lt_two_pow_self (n:=N)
    have hi := BufferMachine.inputWidth_le_width N B
    dsimp only [BufferMachine.inputWidth] at hi
    omega
  have hcost := BufferMachine.loop_cost N B
  have hmain : BufferMachine.costBound N B ≤ BufferMachine.loopCoefficient*(W+1033)^3 := by
    calc
      _ ≤ BufferMachine.loopCoefficient*(W+1033)*(W+1033)^2 := hcost.trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) 2))
      _ = _ := by ring
  have ha := Nat.mul_le_mul_left (3000*8^prepareSpans.length) (square_le_cube W 2 (by decide))
  have hl := Nat.mul_le_mul_left (3000*8^loadBuffer.length) (square_le_cube W 2 (by decide))
  have hr := Nat.mul_le_mul_left (3000*8^BufferMachine.restartInstructions.length) (square_le_cube W 1033 (by decide))
  have hz := Nat.mul_le_mul_left (3000*8^saveBuffer.length) (square_le_cube W 2 (by decide))
  unfold bufferStageCost bufferCoefficient BufferMachine.resetCost BufferMachine.arithmeticCost
  dsimp only [N] at hmain
  rw [show W+1031+2=W+1033 by omega]
  nlinarith only [ha,hl,hr,hmain,hz]

theorem stopping_cost_bound (W : ℕ) : stoppingCost W ≤ stoppingCoefficient*(W+1033)^3 := by
  have hsq := square_le_cube W 2 (by decide)
  have hd := Nat.mul_le_mul_left (3000*8^7+2^100+50) hsq
  have hp := Nat.mul_le_mul_left (3000*8^tailPrepare.length) hsq
  have ht := Nat.mul_le_mul_left (tests.length*(3000*8^4+8000)) hsq
  have hone : 1 ≤ (W+1033)^3 := Nat.one_le_pow _ _ (by omega)
  have hextra := Nat.mul_le_mul_left (tests.length*2+2) hone
  unfold stoppingCost stoppingCoefficient decayCost AllComparisons.unitCost
  nlinarith only [hd,hp,ht,hextra]

theorem stage_cost_bound (D : Data) (hD : D.Positive) (e k W : ℕ)
    (hw : stageWidth D hD e k ≤ W) : stageCost D hD e k W ≤ stageCoefficient*(W+1033)^3 := by
  have hp := Nat.two_pow_pos k
  dsimp only [stageWidth] at hw
  have hs := spacing_cost_bound D hD e k W (baseWidth D hD e k) (by omega)
  have ht := tau_cost_bound D hD e k W (baseWidth D hD e k) (by omega) (by omega)
  have hb := buffer_cost_bound D hD e k W (bufferWidth D hD e k) (by omega)
  have hf := stopping_cost_bound W
  unfold stageCost stageCoefficient
  nlinarith only [hs,ht,hb,hf]

#print axioms stage_cost_bound
end Maxwell.Continuum.Parameters.OuterMachine
