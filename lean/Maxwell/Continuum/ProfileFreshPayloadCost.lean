import Maxwell.Continuum.ProfileFreshPayload

/-! Charged fresh-workspace installation preserves the existing polynomial
profile runtime exponent. The bound includes retained output capture. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] producerEmitCost profileDegree profileGrid profileWorkBits

private theorem power_mono {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b:=
  Nat.pow_le_pow_right (by decide) h

theorem freshStartupCost_precision (N heap : ℕ) (hh : heap.bits.length≤producerSize N) :
    freshStartupCost N heap≤2^1001*(N+1)^4:=by
  have hN := (producerSize_input_bounds N).2.1
  have hx : 1≤(N+1)^2:=one_le_pow₀ (by omega)
  have width : entryWidth N heap+2≤2^48*(N+1)^2:=by
    unfold entryWidth
    unfold producerSize at hh hN
    omega
  have initCost : Initialize.cost dftRegisters≤2^1000:=by decide +kernel
  have hfour : 1≤(N+1)^4:=one_le_pow₀ (by omega)
  have arithmetic : 3000*8^2*(entryWidth N heap+2)^2≤2^1000*(N+1)^4:=by
    calc
      _≤3000*8^2*(2^48*(N+1)^2)^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left width 2)
      _≤2^114*(N+1)^4:=by ring_nf;omega
      _≤_:=Nat.mul_le_mul_right _ (power_mono (by decide))
  unfold freshStartupCost
  calc
    _≤2^1000*(N+1)^4+2^1000*(N+1)^4:=Nat.add_le_add arithmetic
      (initCost.trans (Nat.le_mul_of_pos_right _ (by omega)))
    _=2^1001*(N+1)^4:=by rw [←two_mul,←Nat.mul_assoc,←pow_succ']

theorem freshPayloadCost_precision (N heap : ℕ) (hh : heap.bits.length≤producerSize N) :
    freshPayloadCost N heap≤2^84007*(N+1)^2088:=by
  have startup := freshStartupCost_precision N heap hh
  have main := producerEmitCost_precision N 0 (Nat.zero_le _)
  have small : 2^1001*(N+1)^4≤2^84003*(N+1)^2088:=Nat.mul_le_mul
    (power_mono (by decide)) (Nat.pow_le_pow_right (by omega) (by decide))
  have positive : 1≤(N+1)^2088:=one_le_pow₀ (by omega)
  have seven : 7≤2^84003*(N+1)^2088:=by
    have hc : 7≤(2:ℕ)^84003:=(by decide : 7≤2^3).trans (power_mono (by decide))
    exact hc.trans (Nat.le_mul_of_pos_right _ (by omega))
  unfold freshPayloadCost
  calc
    _≤8*(2^84003*(N+1)^2088):=by omega
    _≤16*(2^84003*(N+1)^2088):=Nat.mul_le_mul_right _ (by decide)
    _=2^84007*(N+1)^2088:=by rw [←Nat.mul_assoc,show (16:ℕ)=2^4 from rfl,←pow_add]

#print axioms freshPayloadCost_precision
end Maxwell.Continuum.Profile.Runtime
