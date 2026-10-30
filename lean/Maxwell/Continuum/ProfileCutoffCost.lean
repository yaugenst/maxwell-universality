import Maxwell.Continuum.ProfileGeneratedCutoff
import Maxwell.Continuum.CutoffCacheCost
import Maxwell.Continuum.ProfileAllocatedCost

/-! Explicit polynomial bounds for the complete generated cutoff cache,
including both allocations, coefficient generation and antiderivative pass. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Calibration.RawCutoff
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget

private theorem coefficient_le {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b :=
  Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h

theorem antiderivativeCacheCost_polynomial (D W : ℕ) :
    antiderivativePreparationCost D (monomialStorageWidth D W) D.bits.length
      (monomialWorkingWidth D W)≤2^194*(D+W+4)^10 := by
  let S := monomialStorageWidth D W
  let B := monomialWorkingWidth D W
  let Z := D+W+4
  have hz : 1≤Z := by dsimp [Z];omega
  have hd : D.bits.length≤S := by
    have h := cache_nat_bits_le D
    dsimp [S,monomialStorageWidth]
    omega
  have base := antiderivativePreparationCost_polynomial D S D.bits.length S hd le_rfl
  have adjusted : antiderivativePreparationCost D S D.bits.length B≤
      antiderivativePreparationCost D S D.bits.length S+6*B := by
    unfold antiderivativePreparationCost scalePreparationCost
    omega
  have hw : B+18≤2^10*Z^2 := monomialWorkingWidth_quadratic D W
  have hs : D+S+4≤2^10*Z^2 := by
    have hb : D+S+4≤B+18 := by dsimp [S,B,monomialWorkingWidth,monomialStorageWidth];omega
    exact hb.trans hw
  have main : antiderivativePreparationCost D S D.bits.length S≤2^192*Z^10 := by
    calc
      _≤2^142*(D+S+4)^5 := base
      _≤2^142*(2^10*Z^2)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 5)
      _=_ := by ring
  have hpower : Z^2≤Z^10 := Nat.pow_le_pow_right hz (by decide)
  change _≤2^194*Z^10
  nlinarith only [adjusted,main,hw,hpower]

theorem cutoffCacheCost_polynomial (N : ℕ) :
    cutoffCacheCost N≤2^196*(profileDegree N+cacheSourceWidth N+4)^10 := by
  have hm := monomialCacheCost_polynomial N
  have ha := antiderivativeCacheCost_polynomial (profileDegree N) (cacheSourceWidth N)
  have hp : (profileDegree N+cacheSourceWidth N+4)^8≤
      (profileDegree N+cacheSourceWidth N+4)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold cutoffCacheCost
  nlinarith only [hm,ha,hp]

private theorem cutoff_power (X : ℕ) :
    2^196*(2^1412*X^36)^10=2^14316*X^360 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

theorem cutoffCacheCost_precision (N : ℕ) :
    cutoffCacheCost N≤2^84000*(N+1)^2088 := by
  obtain ⟨hB,hW,hU,hM⟩ := commonBudget_bounds N
  have hm : cacheSourceWidth N≤commonBudget N := hM
  have hd : profileDegree N≤commonBudget N := (producerSize_bounds N).2.2.1.trans hU
  have hc := commonBudget_polynomial N
  have hp : 1≤(N+1)^36 := one_le_pow₀ (by omega)
  have scaled : profileDegree N+cacheSourceWidth N+4≤2^1412*(N+1)^36 := by omega
  calc
    _≤2^196*(profileDegree N+cacheSourceWidth N+4)^10 := cutoffCacheCost_polynomial N
    _≤2^196*(2^1412*(N+1)^36)^10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scaled 10)
    _=2^14316*(N+1)^360 := cutoff_power _
    _≤_ := Nat.mul_le_mul (coefficient_le (by decide : 14316≤84000))
      (Nat.pow_le_pow_right (Nat.succ_pos N) (by decide : 360≤2088))

theorem generatedCutoffCost_precision (N len : ℕ) (hlen : len≤runtimeBudget N) :
    generatedCutoffCost N len≤2^84003*(N+1)^2088 := by
  have hp := producerCost_precision N len hlen
  have hc := cutoffCacheCost_precision N
  have he : (2:ℕ)^84003=2^84002*2 := by rw [show 84003=84002+1 from rfl,pow_succ]
  have hpow : (2:ℕ)^84000≤2^84002 := coefficient_le (by decide : 84000≤84002)
  have hc' := hc.trans (Nat.mul_le_mul_right ((N+1)^2088) hpow)
  unfold generatedCutoffCost
  rw [he]
  omega

#print axioms generatedCutoffCost_precision
end Maxwell.Continuum.Profile.Runtime
