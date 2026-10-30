import Maxwell.Continuum.ProfileTableCost

/-! An explicit polynomial cost for the actual fixed profile-table
constructor. This bounds unreduced arithmetic, not merely index counts. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid

def commonBudget (N : ℕ) : ℕ := 2^10*runtimeBudget N

theorem commonBudget_bounds (N : ℕ) :
    20≤commonBudget N ∧ runtimeBudget N≤commonBudget N ∧ producerSize N≤commonBudget N ∧
      encodedTableWidth (profileDegree N) (runtimeBudget N)≤commonBudget N := by
  have hb := (runtimeBudget_parameters N).1
  have base := workingBudget_base (producerSize N)
  have hd := (producerSize_bounds N).2.2.1
  change producerSize N+1≤runtimeBudget N at base
  unfold commonBudget encodedTableWidth correctionWorkingWidth endpointWorkingWidth
  omega

theorem commonBudget_polynomial (N : ℕ) : commonBudget N≤2^1410*(N+1)^36 := by
  calc
    _≤2^10*(2^1400*(N+1)^36) := Nat.mul_le_mul_left _ (runtimeBudget_polynomial N)
    _=_ := by ring

private theorem table_power (X : ℕ) : 2^1412*(2^1410*X^36)^58=2^83192*X^2088 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

private theorem startup_power (X : ℕ) : 2^170*(2^1400*X^36)^2=2^2970*X^72 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

private theorem coefficient_le {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b :=
  Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h

theorem encodedTableCost_precision (N : ℕ) :
    encodedTableCost (profileGrid N) (profileDegree N) (profileWorkBits N) (producerSize N)
      (runtimeBudget N) (profileDegree N).bits.length≤2^84000*(N+1)^2088 := by
  obtain ⟨hb,hW,hU,hm⟩ := commonBudget_bounds N
  obtain ⟨_,hg,hD,hP⟩ := producerSize_bounds N
  obtain ⟨_,hr,hn,_,_⟩ := runtimeBudget_parameters N
  have cost := encodedTableCost_cap (profileGrid N) (profileDegree N) (profileWorkBits N)
    (producerSize N) (runtimeBudget N) (profileDegree N).bits.length (commonBudget N)
    (hg.trans hU) (hD.trans hU) (hP.trans hU) hW (hn.trans hW) (hr.trans hW) hm hb
  calc
    _≤2^1412*(commonBudget N)^58 := cost
    _≤2^1412*(2^1410*(N+1)^36)^58 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (commonBudget_polynomial N) 58)
    _=2^83192*(N+1)^2088 := table_power _
    _≤_ := Nat.mul_le_mul_right _ (coefficient_le (by decide : 83192≤84000))

theorem startupCost_cap (N W len : ℕ) (hW : 1≤W) (hP : profileWorkBits N≤W)
    (hD : (profileDegree N).bits.length≤W) (hlen : len≤W) :
    startupCost N W len≤2^170*W^2 := by
  have one : 1≤W^2 := one_le_pow₀ hW
  have lin : W≤W^2 := Nat.le_self_pow (by decide) _
  have dimension : 2^120*(W+2)^2≤2^124*W^2 := by
    calc
      _≤2^120*(4*W)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  have words : stageCost (dimensionWidth W)≤2^164*W^2 := by
    have hb : dimensionWidth W+2≤2^34*W := by unfold dimensionWidth;omega
    unfold stageCost
    calc
      _≤2^96*(2^34*W)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
      _=_ := by ring
  have power : 2^10*(profileWorkBits N+2)^2≤2^14*W^2 := by
    calc
      _≤2^10*(4*W)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  unfold startupCost parameterCost
  omega

theorem initializedTableCost_precision (N len : ℕ) (hlen : len≤runtimeBudget N) :
    initializedTableCost N (runtimeBudget N) (runtimeBudget N) len≤2^84001*(N+1)^2088 := by
  obtain ⟨hW,_,hD,_,_⟩ := runtimeBudget_parameters N
  have hp := (producerSize_bounds N).2.2.2
  have base := workingBudget_base (producerSize N)
  change producerSize N+1≤runtimeBudget N at base
  have startup : startupCost N (runtimeBudget N) len≤2^2970*(N+1)^72 := by
    calc
      _≤2^170*(runtimeBudget N)^2 := startupCost_cap N _ len hW (by omega) hD hlen
      _≤2^170*(2^1400*(N+1)^36)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (runtimeBudget_polynomial N) 2)
      _=_ := startup_power _
  have startup' : startupCost N (runtimeBudget N) len≤2^84000*(N+1)^2088 :=
    startup.trans (Nat.mul_le_mul
      (coefficient_le (by decide : 2970≤84000))
      (Nat.pow_le_pow_right (Nat.succ_pos N) (by decide : 72≤2088)))
  have table := encodedTableCost_precision N
  unfold initializedTableCost
  have he : (2:ℕ)^84001=2^84000*2 := by rw [show 84001=84000+1 from rfl,pow_succ]
  rw [he]
  omega

#print axioms initializedTableCost_precision
end Maxwell.Continuum.Profile.Runtime
