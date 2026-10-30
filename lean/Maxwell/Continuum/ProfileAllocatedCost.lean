import Maxwell.Continuum.ProfileProducerAllocated

/-! Allocation and exact profile computation satisfy one explicit
polynomial bound in the requested precision. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget

private theorem coefficient_le {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b :=
  Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h

private theorem allocation_power (X : ℕ) : 2^181*(2^1412*X^36)^2=2^3005*X^72 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

theorem allocationCost_precision (N : ℕ) :
    allocationCost N (profileDegree N) (producerSize N)≤2^84000*(N+1)^2088 := by
  obtain ⟨hB,hW,hU,hM⟩ := commonBudget_bounds N
  have wm : bufferWidth N (profileDegree N)≤commonBudget N := hM
  have hb (n : ℕ) : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have arithmetic : allocationArithmeticCost (producerSize N)≤2^180*(commonBudget N+2)^2 :=
    (allocationArithmeticCost_polynomial _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right hU 2) 2))
  have clockW := clockCost_bound (runtimeBudget N) (commonBudget N) hW ((hb _).trans hW)
  have clockM := clockCost_bound (bufferWidth N (profileDegree N)) (commonBudget N) wm ((hb _).trans wm)
  have total : allocationCost N (profileDegree N) (producerSize N)≤2^181*(commonBudget N+2)^2 := by
    unfold allocationCost
    nlinarith only [arithmetic,clockW,clockM,Nat.zero_le (commonBudget N)]
  have hp : 1≤(N+1)^36 := one_le_pow₀ (by omega)
  have scaled : commonBudget N+2≤2^1412*(N+1)^36 := by
    have hc := commonBudget_polynomial N
    omega
  calc
    _≤2^181*(commonBudget N+2)^2 := total
    _≤2^181*(2^1412*(N+1)^36)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scaled 2)
    _=2^3005*(N+1)^72 := allocation_power _
    _≤_ := Nat.mul_le_mul (coefficient_le (by decide : 3005≤84000))
      (Nat.pow_le_pow_right (Nat.succ_pos N) (by decide : 72≤2088))

theorem producerCost_precision (N len : ℕ) (hlen : len≤runtimeBudget N) :
    producerCost N len≤2^84002*(N+1)^2088 := by
  have htable := initializedTableCost_precision N len hlen
  have halloc := allocationCost_precision N
  have sum : producerCost N len=initializedTableCost N (runtimeBudget N) (runtimeBudget N) len+
      allocationCost N (profileDegree N) (producerSize N) := by
    unfold producerCost initializedTableCost
    omega
  have h1 : (2:ℕ)^84001=2^84000*2 := by rw [show 84001=84000+1 from rfl,pow_succ]
  have h2 : (2:ℕ)^84002=2^84000*4 := by
    rw [show 84002=84000+1+1 from rfl,pow_succ,pow_succ]
    simp only [Nat.mul_assoc,show (2:ℕ)*2=4 from rfl]
  rw [sum,h2]
  rw [h1] at htable
  omega

#print axioms allocationCost_precision
#print axioms producerCost_precision
end Maxwell.Continuum.Profile.Runtime
