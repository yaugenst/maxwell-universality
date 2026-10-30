import Maxwell.Continuum.ProfileStoredEmission
import Maxwell.Continuum.ProfileAllocatedCost

/-! The executed profile serializer fits inside the same polynomial bound as
its actual coefficient producer, including the raw-word arithmetic costs. -/
namespace Maxwell.Continuum.Profile.Runtime
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits commonBudget runtimeBudget producerCost

private theorem coefficient_le {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b :=
  Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h

private theorem emission_power (X : ℕ) : 2^159*(2^1410*X^36)^3=2^4389*X^108 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

theorem emitTableCost_precision (N : ℕ) :
    emitTableCost N (runtimeBudget N)≤2^4500*(N+1)^108 := by
  obtain ⟨hC,hW,hU,hB⟩ := commonBudget_bounds N
  have hD := (producerSize_bounds N).2.2.1.trans hU
  have hP := (producerSize_bounds N).2.2.2.trans hU
  have hfirst : profileDegree N+1≤2*commonBudget N := by omega
  have hsecond : profileWorkBits N+encodedTableWidth (profileDegree N) (runtimeBudget N)+6≤
      3*commonBudget N := by omega
  calc
    _≤2^154*(2*commonBudget N)*(3*commonBudget N)^2 := by
      unfold emitTableCost
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hfirst) (Nat.pow_le_pow_left hsecond 2)
    _≤2^159*(commonBudget N)^3 := by ring_nf;omega
    _≤2^159*(2^1410*(N+1)^36)^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (commonBudget_polynomial N) 3)
    _=2^4389*(N+1)^108 := emission_power _
    _≤_ := Nat.mul_le_mul_right _ (coefficient_le (by decide : 4389≤4500))

def producerEmitCost (N oldLength : ℕ) : ℕ := producerCost N oldLength+emitTableCost N (runtimeBudget N)

theorem producerEmitCost_precision (N len : ℕ) (hlen : len≤runtimeBudget N) :
    producerEmitCost N len≤2^84003*(N+1)^2088 := by
  have hp := producerCost_precision N len hlen
  have he := emitTableCost_precision N
  have hm : 2^4500*(N+1)^108≤2^84002*(N+1)^2088 :=
    Nat.mul_le_mul (coefficient_le (by decide : 4500≤84002))
      (Nat.pow_le_pow_right (by omega : 0<N+1) (by decide : 108≤2088))
  unfold producerEmitCost
  calc
    _≤2^84002*(N+1)^2088+2^84002*(N+1)^2088 := Nat.add_le_add hp (he.trans hm)
    _=2^84003*(N+1)^2088 := by
      rw [←two_mul,←Nat.mul_assoc,←pow_succ']

#print axioms producerEmitCost_precision
end Maxwell.Continuum.Profile.Runtime
