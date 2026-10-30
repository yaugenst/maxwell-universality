import Maxwell.Continuum.ChebyshevWaveRuntimeSumStep
import Maxwell.Continuum.PhaseRuntimeDataflowCost
import Maxwell.Continuum.DyadicFloorCost

/-! Charged cost of the fixed wave summand, with a separate bound on its
actual intermediate word widths. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem arithmetic_cost_budget (U B : ℕ) (hU : 1 ≤ U) (hB : B ≤ U) :
    operationCost B ≤ 2^104*U^14 ∧ RationalDataflow.stageCost B ≤ 2^100*U^14 := by
  have hp : U^2 ≤ U^14 := Nat.pow_le_pow_right hU (by decide)
  constructor
  · calc
      _ ≤ 2^100*(4*U)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 2^104*U^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  · calc
      _ ≤ 2^96*(4*U)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 2^100*U^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem enlarged_arithmetic_cost_budget (U B : ℕ) (hU : 1 ≤ U) (hB : B ≤ 256*U) :
    operationCost B ≤ 2^118*U^14 := by
  have hp : U^2 ≤ U^14 := Nat.pow_le_pow_right hU (by decide)
  calc
    _ ≤ 2^100*(512*U)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^118*U^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem floor_cost_budget (U P B : ℕ) (hU : 1 ≤ U) (hP : P ≤ U) (hB : B ≤ U) :
    DyadicFloor.costBound P B ≤ 2^146*U^14 := by
  have hp : U^2 ≤ U^14 := Nat.pow_le_pow_right hU (by decide)
  calc
    _ ≤ 2^140*(P+B+4)^2 := DyadicFloor.costBound_polynomial P B
    _ ≤ 2^140*(8*U)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^146*U^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem phase_cost_budget (U Q N B : ℕ) (h : Q+N+B+12 ≤ 32*U) :
    Phase.Runtime.costBound Q N B ≤ 2^392*U^14 := by
  calc
    _ ≤ 2^322*(Q+N+B+12)^14 := Phase.Runtime.costBound_polynomial Q N B
    _ ≤ 2^322*(32*U)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 14)
    _ = _ := by ring

theorem sample_cost_budget (Q P V U : ℕ) (hU : 1 ≤ U) (hQ : Q ≤ U) (hP : P ≤ U)
    (hphase : Calibration.phaseBits Q (P+4) ≤ U) (hV : V ≤ U) :
    sampleCost Q P V ≤ 2^400*U^14 := by
  have h1 := phase_cost_budget U 1 (Calibration.phaseBits Q (P+4)) V (by omega)
  have h2 := phase_cost_budget U (2*(Q+1)) (P+4) V (by omega)
  have hstage := (arithmetic_cost_budget U V hU hV).2
  have hp : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have hlinear : 64*(V+1) ≤ 128*U^14 := by omega
  unfold sampleCost
  omega

theorem product_cost_budget (Q P W B oldQ oldN U : ℕ)
    (hU : 1 ≤ U) (hQ : Q ≤ U) (hP : P ≤ U) (hphase : Calibration.phaseBits Q (P+4) ≤ U)
    (hsample : sampleWidth Q P W B oldQ oldN ≤ U) (hproduct : productWidth Q P W B ≤ U) :
    productCost Q P W B oldQ oldN ≤ 2^408*U^14 := by
  have hsampleCost := sample_cost_budget Q P _ U hU hQ hP hphase hsample
  have hfloor := floor_cost_budget U 0 _ hU (Nat.zero_le _) hproduct
  have hstage := (arithmetic_cost_budget U _ hU hproduct).2
  have hphaseCost := phase_cost_budget U 1 P (productWidth Q P W B) (by omega)
  have hwork := enlarged_arithmetic_cost_budget U (64*(productWidth Q P W B+1)) hU (by omega)
  have hp : U ≤ U^14 := Nat.le_self_pow (by decide) U
  have hone : 1 ≤ U^14 := one_le_pow₀ hU
  have hlinear : 64*(productWidth Q P W B+1) ≤ 128*U^14 := by omega
  unfold productCost
  omega

theorem sum_step_cost_budget (Q P W B U : ℕ)
    (hU : 1 ≤ U) (hQ : Q ≤ U) (hP : P ≤ U) (hphase : Calibration.phaseBits Q (P+4) ≤ U)
    (hB : B ≤ U) (hwork : productWorkWidth Q P (5*(W+1)) ≤ U)
    (hsample : sampleWidth Q P (5*(W+1)) (B+5*(W+1)) 1 P ≤ U)
    (hproduct : productWidth Q P (5*(W+1)) (B+5*(W+1)) ≤ U) :
    sumStepCost Q P W B 1 P ≤ 2^410*U^14 := by
  have hprepare := enlarged_arithmetic_cost_budget U (64*(B+1)) hU (by omega)
  have hprod := product_cost_budget Q P (5*(W+1)) (B+5*(W+1)) 1 P U hU hQ hP hphase hsample hproduct
  have haccum := enlarged_arithmetic_cost_budget U (64*(B+productWorkWidth Q P (5*(W+1))+1))
    hU (by omega)
  have hone : 1 ≤ U^14 := one_le_pow₀ hU
  unfold sumStepCost
  omega

#print axioms sum_step_cost_budget
end Maxwell.Continuum.Profile.WaveMachine.Runtime
