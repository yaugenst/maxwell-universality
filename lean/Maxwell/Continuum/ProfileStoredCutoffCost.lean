import Maxwell.Continuum.ProfileStoredCutoff
import Maxwell.Continuum.ProfileCutoffCost

/-! The cursor handoff is included in the complete cutoff producer bound. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Calibration.RawCutoff
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget

private theorem coefficient_le {a b : ℕ} (h : a≤b) : (2:ℕ)^a≤2^b :=
  Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h

theorem cacheDimensionSum_precision (N : ℕ) :
    profileDegree N+cacheSourceWidth N+4≤2^1412*(N+1)^36 := by
  obtain ⟨hB,hW,hU,hM⟩ := commonBudget_bounds N
  have hm : cacheSourceWidth N≤commonBudget N := hM
  have hd : profileDegree N≤commonBudget N := (producerSize_bounds N).2.2.1.trans hU
  have hc := commonBudget_polynomial N
  have hp : 1≤(N+1)^36 := one_le_pow₀ (by omega)
  omega

private theorem finish_power (X : ℕ) : 2^124*(2^1412*X^36)^4=2^5772*X^144 := by
  simp only [mul_pow,←pow_mul,←mul_assoc,←pow_add]

theorem cacheFinishCost_precision (N : ℕ) :
    2^104*(monomialWorkingWidth (profileDegree N) (cacheSourceWidth N)+8)^2≤
      2^84000*(N+1)^2088 := by
  let Z := profileDegree N+cacheSourceWidth N+4
  have hb : monomialWorkingWidth (profileDegree N) (cacheSourceWidth N)+8≤2^10*Z^2 := by
    have h := monomialWorkingWidth_quadratic (profileDegree N) (cacheSourceWidth N)
    change monomialWorkingWidth (profileDegree N) (cacheSourceWidth N)+18≤2^10*Z^2 at h
    omega
  calc
    _≤2^104*(2^10*Z^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
    _=2^124*Z^4 := by ring
    _≤2^124*(2^1412*(N+1)^36)^4 := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (cacheDimensionSum_precision N) 4)
    _=2^5772*(N+1)^144 := finish_power _
    _≤_ := Nat.mul_le_mul (coefficient_le (by decide : 5772≤84000))
      (Nat.pow_le_pow_right (Nat.succ_pos N) (by decide : 144≤2088))

theorem storedCutoffCost_precision (N len : ℕ) (hlen : len≤runtimeBudget N) :
    storedCutoffCost N len≤2^84004*(N+1)^2088 := by
  have hp := generatedCutoffCost_precision N len hlen
  have hc := (cacheFinishCost_precision N).trans
    (Nat.mul_le_mul_right ((N+1)^2088) (coefficient_le (by decide : 84000≤84003)))
  have he : (2:ℕ)^84004=2^84003*2 := by rw [show 84004=84003+1 from rfl,pow_succ]
  unfold storedCutoffCost
  rw [he]
  omega

#print axioms storedCutoffCost_precision
end Maxwell.Continuum.Profile.Runtime
