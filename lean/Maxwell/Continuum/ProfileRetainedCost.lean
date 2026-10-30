import Maxwell.Continuum.ProfileRetainedPayload

/-! The retained profile uses the same polynomial precision exponent as
the producer, including the captured writes and final rewind. -/
namespace Maxwell.Continuum.Profile.Runtime
set_option exponentiation.threshold 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] producerEmitCost

theorem retainedPayload_cost (N len : ℕ) (hlen : len≤runtimeBudget N) :
    6*producerEmitCost N len+7≤2^84007*(N+1)^2088 := by
  have h := producerEmitCost_precision N len hlen
  have hpow : 1≤2^84003*(N+1)^2088 :=
    one_le_mul (one_le_pow₀ (by decide)) (one_le_pow₀ (by omega))
  have he : (2:ℕ)^84007=16*2^84003 := by
    rw [show 84007=4+84003 from rfl,pow_add]
    exact congrArg (fun n : ℕ => n*2^84003) (by decide : (2:ℕ)^4=16)
  have step (a b : ℕ) (hab : a≤b) (hb : 1≤b) : 6*a+7≤16*b := by omega
  simpa only [he,mul_assoc] using step _ _ h hpow

#print axioms retainedPayload_cost
end Maxwell.Continuum.Profile.Runtime
