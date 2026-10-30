import Maxwell.Continuum.ChebyshevWaveCacheWidthBudget
import Maxwell.Continuum.ChebyshevWaveRuntimeCostBudget

/-! Uniform charged polynomial time for the full fixed wave-cache program. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 16384

theorem sum_cost_budget (Q P W grid U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) : sumCost Q P grid W ≤ 2^412*(grid+1)*U^14 := by
  let H := (grid+1)*U^14
  have hu : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by dsimp [H];nlinarith only [Nat.zero_le grid,Nat.zero_le (U^14)]
  have hg' : grid.bits.length ≤ U := hg.trans h.w_le
  have hs := sum_step_cost_budget Q P W (sumBankWidth Q P W grid) U h.positive h.q_le h.p_le
    h.phase_le h.summation h.summand h.sample h.product
  have hmain : grid*sumStepCost Q P W (sumBankWidth Q P W grid) 1 P ≤ 2^410*H := by
    calc
      _ ≤ grid*(2^410*U^14) := Nat.mul_le_mul_left _ hs
      _ ≤ (grid+1)*(2^410*U^14) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by dsimp [H];ring
  have hcounter : (grid+1)*(13*grid.bits.length+15) ≤ 28*H := by
    calc
      _ ≤ (grid+1)*(28*U^14) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by dsimp [H];ring
  have hcleanup : 6*grid.bits.length+4 ≤ 10*H := by omega
  suffices hb : sumCost Q P grid W ≤ 2^412*H by simpa only [H,Nat.mul_assoc] using hb
  unfold sumCost
  omega

theorem coefficient_cost_budget (Q P W grid U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) : coefficientCost Q P grid W ≤ 2^414*(grid+1)*U^14 := by
  let H := (grid+1)*U^14
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by dsimp [H];nlinarith only [Nat.zero_le grid,Nat.zero_le (U^14)]
  have hs : sumCost Q P grid W ≤ 2^412*H := by
    simpa only [H,Nat.mul_assoc] using sum_cost_budget Q P W grid U h hg
  have ha := (arithmetic_cost_budget U (coefficientWidth Q P grid W) h.positive h.coefficient).1
  suffices hb : coefficientCost Q P grid W ≤ 2^414*H by simpa only [H,Nat.mul_assoc] using hb
  change sumCost Q P grid W+2*operationCost (coefficientWidth Q P grid W)+1 ≤ _
  omega

theorem cosine_cost_budget (Q P W grid U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) : cosineCost Q P grid W ≤ 2^418*(grid+1)*U^14 := by
  let H := (grid+1)*U^14
  let B := coefficientWidth Q P grid W
  have hu : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by dsimp [H];nlinarith only [Nat.zero_le grid,Nat.zero_le (U^14)]
  have hc : coefficientCost Q P grid W ≤ 2^414*H := by
    simpa only [H,Nat.mul_assoc] using coefficient_cost_budget Q P W grid U h hg
  have hB : B ≤ U := h.coefficient
  have ha := (arithmetic_cost_budget U (4*(B+1)) h.positive (by have := h.cosine;dsimp [B];omega)).1
  have hb := (arithmetic_cost_budget U (256*(B+1)) h.positive h.cosine).1
  have hg' : grid.bits.length ≤ U := hg.trans h.w_le
  suffices hb : cosineCost Q P grid W ≤ 2^418*H by simpa only [H,Nat.mul_assoc] using hb
  change 2*coefficientCost Q P grid W+252*(B+1)+(12*operationCost (4*(B+1))+1)+
    (15*grid.bits.length+21)+(36*B+24)+(8*operationCost (256*(B+1))+1) ≤ _
  omega

theorem encoded_cost_budget (Q P W grid U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) : encodedCost Q P grid W ≤ 2^420*(grid+1)*U^14 := by
  let H := (grid+1)*U^14
  let B := 256*(coefficientWidth Q P grid W+1)
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by dsimp [H];nlinarith only [Nat.zero_le grid,Nat.zero_le (U^14)]
  have hc : cosineCost Q P grid W ≤ 2^418*H := by
    simpa only [H,Nat.mul_assoc] using cosine_cost_budget Q P W grid U h hg
  have hB : B ≤ U := h.cosine
  have hB' : 2*B+P+4 ≤ U := h.encoded
  have hf0 := floor_cost_budget U P B h.positive h.p_le hB
  have hf1 := floor_cost_budget U P (2*B+P+3) h.positive h.p_le (by omega)
  have ha0 := (arithmetic_cost_budget U (2*B+P+3) h.positive (by omega)).1
  have ha1 := (arithmetic_cost_budget U (2*B+P+3+1) h.positive (by omega)).1
  suffices hb : encodedCost Q P grid W ≤ 2^420*H by simpa only [H,Nat.mul_assoc] using hb
  change cosineCost Q P grid W+(DyadicFloor.costBound P B+DyadicFloor.costBound P (2*B+P+3))+
    (operationCost (2*B+P+3)+operationCost (2*B+P+3+1)) ≤ _
  omega

theorem cache_step_cost_budget (Q P W grid U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) :
    cacheStepCost Q P grid W (cacheBankWidth Q P grid W) ≤ 2^422*(grid+1)*U^14 := by
  let H := (grid+1)*U^14
  have hu : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by dsimp [H];nlinarith only [Nat.zero_le grid,Nat.zero_le (U^14)]
  have he : encodedCost Q P grid W ≤ 2^420*H := by
    simpa only [H,Nat.mul_assoc] using encoded_cost_budget Q P W grid U h hg
  have ha := (arithmetic_cost_budget U (cacheBankWidth Q P grid W+1) h.positive h.bank).1
  have hg' : grid.bits.length ≤ U := hg.trans h.w_le
  have hload : cacheLoadCost (cacheBankWidth Q P grid W) W grid ≤ 2^110*H := by
    unfold cacheLoadCost
    have := h.w_le
    omega
  have hwrite : rowPlanCost 2 1 W cacheWritePlan ≤ 2^40*U^14 := by
    have hp : U^2 ≤ U^14 := Nat.pow_le_pow_right h.positive (by decide)
    have hw : (W+8)^2 ≤ (16*U)^2 := Nat.pow_le_pow_left (by have := h.w_le;have := h.positive;omega) 2
    norm_num only [rowPlanCost,cacheWritePlan,List.length_cons,List.length_nil,
      show (2:ℕ).bits.length=2 by decide]
    nlinarith only [hw,hp,h1]
  suffices hb : cacheStepCost Q P grid W (cacheBankWidth Q P grid W) ≤ 2^422*H by
    simpa only [H,Nat.mul_assoc] using hb
  unfold cacheStepCost
  omega

theorem cache_cost_budget (Q P W grid D U : ℕ) (h : RuntimeWidthBudget Q P W grid U)
    (hg : grid.bits.length ≤ W) (hD : D.bits.length ≤ W) :
    cacheCost Q P grid D W ≤ 2^424*(D+1)*(grid+1)*U^14 := by
  let H := (D+1)*(grid+1)*U^14
  have hu : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have h1 : 1 ≤ U^14 := one_le_pow₀ h.positive
  have hH : U^14 ≤ H := by
    have h0 : 1 ≤ (D+1)*(grid+1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    dsimp [H]
    nlinarith only [h0,Nat.zero_le (U^14)]
  have hd : D.bits.length ≤ U := hD.trans h.w_le
  have hstep := cache_step_cost_budget Q P W grid U h hg
  have hmain : D*cacheStepCost Q P grid W (cacheBankWidth Q P grid W) ≤ 2^422*H := by
    calc
      _ ≤ D*(2^422*(grid+1)*U^14) := Nat.mul_le_mul_left _ hstep
      _ ≤ (D+1)*(2^422*(grid+1)*U^14) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by dsimp [H];ring
  have hcounter : (D+1)*(13*D.bits.length+15) ≤ 28*H := by
    calc
      _ ≤ (D+1)*(28*U^14) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (grid+1)*((D+1)*(28*U^14)) := by nlinarith only [Nat.zero_le grid,Nat.zero_le ((D+1)*(28*U^14))]
      _ = _ := by dsimp [H];ring
  have hcleanup : 6*D.bits.length+4 ≤ 10*H := by omega
  suffices hb : cacheCost Q P grid D W ≤ 2^424*H by simpa only [H,Nat.mul_assoc] using hb
  unfold cacheCost
  omega

theorem cache_cost_polynomial (Q P W grid D : ℕ)
    (hg : grid.bits.length ≤ W) (hD : D.bits.length ≤ W) :
    cacheCost Q P grid D W ≤ 2^7200*(D+1)*(grid+1)^15*(frequencyScale Q P W)^56 := by
  have h := cache_cost_budget Q P W grid D (runtimeBudget Q P W grid)
    (actual_runtime_budget Q P W grid) hg hD
  calc
    _ ≤ 2^424*(D+1)*(grid+1)*(runtimeBudget Q P W grid)^14 := h
    _ = 2^7144*(D+1)*(grid+1)^15*(frequencyScale Q P W)^56 := by
      unfold runtimeBudget
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by decide : 7144 ≤ 7200))))

#print axioms cache_cost_polynomial
end Maxwell.Continuum.Profile.WaveMachine.Runtime
