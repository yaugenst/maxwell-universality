import Maxwell.Continuum.CutoffIntegralEvaluation
import Maxwell.Continuum.RationalChebyshevBounds
import Maxwell.Continuum.RationalFiniteWidths
import Maxwell.Continuum.ProfileCoefficientBits

/-! Polynomial rational operand widths for the exact cutoff integrals. -/

namespace Maxwell.Continuum.Calibration

open RationalWords Profile

set_option maxHeartbeats 800000
attribute [local irreducible] encodedCoefficient profileDegree profileWorkBits chebyshevRow

theorem chebyshevRow_width (W j : ℕ) (i : Fin W) :
    Width ((chebyshevRow W j).get i : ℚ) (2*j+2) := by
  have hn := chebyshevRow_natAbs W j i
  have hb := bits_mono hn
  simp only [Nat.size_eq_bits_len,Nat.size_pow] at hb
  apply (width_int ((chebyshevRow W j).get i)).mono
  rw [Nat.size_eq_bits_len]
  omega

theorem chebyshevSquareIntegral_width {a b : ℚ} {W : ℕ}
    (ha : Width a W) (hb : Width b W) (j : ℕ) :
    Width (chebyshevSquareIntegral j a b) (18*(j+1)^2*(W+1)) := by
  have h4 : Width (4 : ℚ) 3 := by constructor <;> decide
  have ht (k : Fin (j+1)) : Width
      ((chebyshevRow (j+1) j).get k * (4 : ℚ)^k.val*
        (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val : ℚ)+1))
      (16*(j+1)*(W+1)) := by
    have hd : Width (2*(k.val : ℚ)+1) (2*k.val+2) := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using width_nat (2*k.val+1)
    have hw := (((chebyshevRow_width (j+1) j k).mul (h4.pow k.val)).mul
      ((hb.pow (2*k.val+1)).sub (ha.pow (2*k.val+1)))).mul (hd.inv (by positivity))
    rw [← div_eq_mul_inv] at hw
    apply hw.mono
    have hk : k.val≤j := by omega
    have hkw := Nat.mul_le_mul_right W hk
    nlinarith only [hk,hkw,Nat.zero_le (j*W)]
  have hs := width_sum Finset.univ
    (fun k : Fin (j+1) => (chebyshevRow (j+1) j).get k*(4 : ℚ)^k.val*
      (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val : ℚ)+1))
    (16*(j+1)*(W+1)) (fun k _ => ht k)
  simp only [Finset.card_univ,Fintype.card_fin] at hs
  change Width (chebyshevSquareIntegral j a b) ((j+1)*(16*(j+1)*(W+1)+1)+1) at hs
  apply hs.mono
  have hJ : 1≤(j+1)^2*(W+1) := Nat.succ_le_of_lt (by positivity)
  have hJ' : j+1≤(j+1)^2*(W+1) := by nlinarith only [Nat.zero_le (j*j),Nat.zero_le (j*W),Nat.zero_le (j*j*W),Nat.zero_le W]
  nlinarith only [hJ,hJ']

theorem encodedCoefficient_width (N j : ℕ) (hj : j<profileDegree N) :
    Width (encodedCoefficient N j).value (272*(N+1)) := by
  have hn := encodedCoefficient_numerator_bits N j hj
  have hd := encodedCoefficient_denominator_bits N
  simp only [Dyadic.numeratorBits,signedBitLength,Codec.unsignedBitLength_eq_size,
    ← Nat.size_eq_bits_len] at hn hd
  have hf := width_fraction (z := (encodedCoefficient N j).numerator)
    (d := 2^profileWorkBits N) (B := 272*(N+1)) (by positivity) (by omega) (by omega)
  simpa only [Dyadic.value,Nat.cast_pow,Nat.cast_ofNat] using hf

def cutoffIntegralWidth (N W : ℕ) : ℕ :=
  profileDegree N*(272*(N+1)+18*(profileDegree N+1)^2*(W+1)+1)+1

theorem cutoffIntegralApprox_width {a b : ℚ} {W : ℕ}
    (ha : Width a W) (hb : Width b W) (N : ℕ) :
    Width (cutoffIntegralApprox N a b) (cutoffIntegralWidth N W) := by
  have ht (j : ℕ) (hj : j∈Finset.range (profileDegree N)) :=
    (encodedCoefficient_width N j (Finset.mem_range.mp hj)).mul (chebyshevSquareIntegral_width ha hb j)
  have hs := width_sum (Finset.range (profileDegree N))
    (fun j => (encodedCoefficient N j).value*chebyshevSquareIntegral j a b)
    (272*(N+1)+18*(profileDegree N+1)^2*(W+1)) (by
      intro j hj
      apply (ht j hj).mono
      gcongr
      exact (Finset.mem_range.mp hj).le)
  simpa only [cutoffIntegralApprox,cutoffIntegralWidth,Finset.card_range] using hs

#print axioms cutoffIntegralApprox_width

end Maxwell.Continuum.Calibration
