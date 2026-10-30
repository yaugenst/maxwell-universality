import Maxwell.Continuum.ProfileRawWidths
import Maxwell.Continuum.ParameterProfileResources

/-! Polynomial specialization of the literal profile producer's stored-word
bound. No canonical rational reduction is used to obtain this estimate. -/
namespace Maxwell.Continuum.Profile.Runtime
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem encodedRawWidth_polynomial (U : ℕ) : encodedRawWidth U≤2^450*(U+1)^18 := by
  simp only [encodedRawWidth,roundedRawWidth,sampledRawWidth,dftRawWidth,dftTermWidth,
    angularRawWidth,angularPhaseWidth,dftPhaseWidth,slopeRawWidth,endpointRawWidth]
  ring_nf
  omega

def producerSize (N : ℕ) : ℕ := 2^46*(N+1)^2

theorem producerSize_bounds (N : ℕ) :
    1≤producerSize N ∧ profileGrid N≤producerSize N ∧
      profileDegree N≤producerSize N ∧ profileWorkBits N≤producerSize N := by
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hn : N+1≤(N+1)^2 := le_self_pow₀ (by omega : 1≤N+1) (by decide : (2:ℕ)≠0)
  have hg := Parameters.profileGrid_bound N
  have hD := profileDegree_bound N
  have hP := Parameters.profileWorkBits_bound N
  unfold producerSize
  omega

theorem encodedParts_width_polynomial (N j : ℕ) (hj : j<profileDegree N) :
    (encodedParts N j).Width (2^1300*(N+1)^36) := by
  obtain ⟨h1,hg,hD,hP⟩ := producerSize_bounds N
  apply (encodedParts_width N j (producerSize N) h1 hg hD hP (by omega)).mono
  apply (encodedRawWidth_polynomial (producerSize N)).trans
  have hpow : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hsize : producerSize N+1≤2^47*(N+1)^2 := by unfold producerSize;omega
  calc
    2^450*(producerSize N+1)^18 ≤ 2^450*(2^47*(N+1)^2)^18 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 18)
    _ = 2^1296*(N+1)^36 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms encodedParts_width_polynomial
end Maxwell.Continuum.Profile.Runtime
