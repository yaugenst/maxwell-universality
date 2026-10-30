import Maxwell.Continuum.ProfileCoefficientBounds
import Maxwell.Continuum.ParameterProfileResources
import Maxwell.Codec.Bounds

/-! Bit lengths of the actual endpoint-corrected dyadic profile data. -/

namespace Maxwell.Continuum.Profile
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local irreducible] encodedCoefficient profileDegree profileWorkBits profileData

theorem encodedCoefficient_value_pow_bound (N j : ℕ) (hj : j<profileDegree N) :
    |(encodedCoefficient N j).value| ≤ (2 : ℚ)^(profileWorkBits N+8) := by
  have hD : (profileDegree N : ℚ)+1 ≤ (2 : ℚ)^Nat.clog 2 (profileDegree N+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (profileDegree N+1)
  have he : 3*Nat.clog 2 (profileDegree N+1) ≤ profileWorkBits N := by
    unfold profileWorkBits
    omega
  calc
    _ ≤ 256*((profileDegree N : ℚ)+1)^3 := encodedCoefficient_bound N j hj
    _ ≤ (2 : ℚ)^8*((2 : ℚ)^Nat.clog 2 (profileDegree N+1))^3 := by
      norm_num only [show (2 : ℚ)^8=256 by norm_num]
      gcongr
    _ = (2 : ℚ)^(8+3*Nat.clog 2 (profileDegree N+1)) := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

theorem encodedCoefficient_numerator_bound (N j : ℕ) (hj : j<profileDegree N) :
    (encodedCoefficient N j).numerator.natAbs ≤ 2^(2*profileWorkBits N+8) := by
  have h := encodedCoefficient_value_pow_bound N j hj
  rw [Dyadic.value,abs_div,abs_pow,abs_of_nonneg (by norm_num : (0:ℚ)≤2)] at h
  have hp : (0 : ℚ)<2^profileWorkBits N := by positivity
  have h' := (div_le_iff₀ hp).mp h
  have he : (2 : ℚ)^(profileWorkBits N+8)*2^profileWorkBits N =
      2^(2*profileWorkBits N+8) := by rw [← pow_add]; congr 1; omega
  rw [he,← Int.cast_abs] at h'
  have hi : |(encodedCoefficient N j).numerator| ≤ (2 : ℤ)^(2*profileWorkBits N+8) := by
    exact_mod_cast h'
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

theorem encodedCoefficient_numerator_bits (N j : ℕ) (hj : j<profileDegree N) :
    (encodedCoefficient N j).numeratorBits ≤ 272*(N+1) := by
  have hb := Codec.unsignedBitLength_mono (encodedCoefficient_numerator_bound N j hj)
  rw [Dyadic.denominator_bitLength] at hb
  have hp := Parameters.profileWorkBits_bound N
  unfold Dyadic.numeratorBits signedBitLength
  omega

theorem encodedCoefficient_denominator_bits (N : ℕ) :
    unsignedBitLength (2^profileWorkBits N) ≤ 132*(N+1) := by
  rw [Dyadic.denominator_bitLength]
  have hp := Parameters.profileWorkBits_bound N
  omega

/-- The actual encoded coefficient words, including self-delimiting integer
codes, use cubic total space in the requested precision. The common dyadic
precision is stored once. -/
def profileBits (N : ℕ) : List Bool :=
  Codec.nat (profileWorkBits N) ++ Codec.list
    (fun d : Dyadic (profileWorkBits N) => Codec.int d.numerator) (profileData N)

theorem profileBits_length (N : ℕ) : (profileBits N).length ≤ 2^41*(N+1)^3 := by
  have hc : ∀ d ∈ profileData N,
      (Codec.int d.numerator).length ≤ 544*(N+1) := by
    intro d hd
    simp only [profileData,List.mem_ofFn] at hd
    obtain ⟨j,rfl⟩ := hd
    rw [Codec.int_length]
    simpa only [Dyadic.numeratorBits,← Nat.mul_assoc,Nat.reduceMul] using
      Nat.mul_le_mul_left 2 (encodedCoefficient_numerator_bits N j j.isLt)
  have hs := Codec.list_length_le
    (fun d : Dyadic (profileWorkBits N) => Codec.int d.numerator)
    (profileData N) (544*(N+1)) hc
  rw [profileData_length] at hs
  have hd := profileDegree_bound N
  have hp := Parameters.profileWorkBits_bound N
  have bits_le_self (n : ℕ) : unsignedBitLength n ≤ n := by
    rw [Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  have hbP := bits_le_self (profileWorkBits N)
  have hbD := bits_le_self (profileDegree N)
  have h1 : 1 ≤ (N+1)^3 := one_le_pow₀ (by omega)
  have h2 : (N+1)^2 ≤ (N+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hN : N+1 ≤ (N+1)^3 := le_self_pow₀ (by omega : 1≤N+1) (by decide : (3:ℕ)≠0)
  have hprod := Nat.mul_le_mul_right (544*(N+1)) hd
  simp only [profileBits,List.length_append,Codec.nat_length]
  nlinarith only [hs,hp,hbP,hbD,hd,hprod,h1,h2,hN]

#print axioms encodedCoefficient_numerator_bits
#print axioms profileBits_length

end Maxwell.Continuum.Profile
