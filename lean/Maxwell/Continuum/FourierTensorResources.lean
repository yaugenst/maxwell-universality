import Maxwell.Continuum.FourierTensorBits
import Maxwell.Continuum.ChebyshevWaveResources

/-! Polylogarithmic size of the actual final vector tensor representation. -/

namespace Maxwell.Continuum.Profile
set_option maxHeartbeats 1000000

def finalVectorBitsCoefficient (C : ℕ) : ℕ :=
  8*(3*(waveDegreeCoefficient C)^3+1)*(2*C+3*wavePrecisionCoefficient C+17)

theorem finalVectorBits_polylog {ι : Type*} {B Q N A C ℓ : ℕ}
    (s : Finset ι) (q : ι→Fin 3→ℚ) (a : Fin 3→ι→ComplexDyadic B)
    (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : ∀ c, (∑ ν∈s, ‖complexDyadicValue (a c ν)‖)≤(2:ℝ)^A)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) (hB : B≤C*ℓ) (hA : A≤C*ℓ) :
    (finalVectorBits s q a Q N).length≤finalVectorBitsCoefficient C*ℓ^25 := by
  have hd := Nat.pow_le_pow_left (waveDegree_polylog hℓ hQ hN) 3
  have hd' : (waveDegree (8*Q) N)^3≤(waveDegreeCoefficient C)^3*ℓ^24 := by
    convert hd using 1
    ring
  have hw := waveWorkBits_polylog hℓ hQ hN
  have h1 : 1≤ℓ^24 := one_le_pow₀ (by omega)
  have hD : 3*(waveDegree (8*Q) N)^3+1≤(3*(waveDegreeCoefficient C)^3+1)*ℓ^24 := by
    nlinarith only [hd',h1]
  have hP : B+3*waveWorkBits (8*Q) N+A+17≤(2*C+3*wavePrecisionCoefficient C+17)*ℓ := by
    nlinarith only [hw,hB,hA,hℓ]
  calc
    _ ≤ 8*(3*(waveDegree (8*Q) N)^3+1)*(B+3*waveWorkBits (8*Q) N+A+17) :=
      finalVectorBits_length s q a Q N A hq ha
    _ ≤ 8*((3*(waveDegreeCoefficient C)^3+1)*ℓ^24)*((2*C+3*wavePrecisionCoefficient C+17)*ℓ) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hD) hP
    _ = _ := by unfold finalVectorBitsCoefficient; ring

theorem finalVectorBits_paper_exponent {ι : Type*} {B Q N A C ℓ : ℕ}
    (s : Finset ι) (q : ι→Fin 3→ℚ) (a : Fin 3→ι→ComplexDyadic B)
    (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : ∀ c, (∑ ν∈s, ‖complexDyadicValue (a c ν)‖)≤(2:ℝ)^A)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) (hB : B≤C*ℓ) (hA : A≤C*ℓ) :
    (finalVectorBits s q a Q N).length≤finalVectorBitsCoefficient C*ℓ^64 :=
  (finalVectorBits_polylog s q a hq ha hℓ hQ hN hB hA).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hℓ (by decide)))

#print axioms finalVectorBits_polylog
#print axioms finalVectorBits_paper_exponent

end Maxwell.Continuum.Profile
