import Maxwell.Continuum.ChebyshevWaveBits

/-! Polynomial logarithmic-size bounds for the literal tensor wave arrays. -/

namespace Maxwell.Continuum.Profile
set_option maxHeartbeats 1000000

def waveDegreeCoefficient (C : ℕ) : ℕ := 2^9*(C+1)
def wavePrecisionCoefficient (C : ℕ) : ℕ := C+Nat.clog 2 (waveDegreeCoefficient C+1)+40
def waveGridCoefficient (C : ℕ) : ℕ := 16*(17*C+wavePrecisionCoefficient C+32)+1
def tensorBitsCoefficient (C : ℕ) : ℕ :=
  8*((waveDegreeCoefficient C)^3+1)*(3*wavePrecisionCoefficient C+17)

theorem waveDegree_polylog {Q N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    waveDegree (8*Q) N≤waveDegreeCoefficient C*ℓ^8 := by
  have hp : ℓ≤ℓ^8 := le_self_pow₀ (by omega : 1≤ℓ) (by decide : (8:ℕ)≠0)
  have h1 : 1≤ℓ^8 := one_le_pow₀ (by omega)
  have hn := hN.trans (Nat.mul_le_mul_left C hp)
  unfold waveDegree waveDegreeCoefficient
  nlinarith only [hQ,hn,h1]

theorem waveWorkBits_polylog {Q N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    waveWorkBits (8*Q) N≤wavePrecisionCoefficient C*ℓ := by
  have hd := waveDegree_polylog hℓ hQ hN
  have h1 : 1≤ℓ^8 := one_le_pow₀ (by omega)
  have hclog : Nat.clog 2 (waveDegree (8*Q) N+1)≤
      Nat.clog 2 (waveDegreeCoefficient C+1)+8*ℓ := by
    apply Nat.clog_le_of_le_pow
    calc
      _ ≤ (waveDegreeCoefficient C+1)*ℓ^8 := by nlinarith only [hd,h1]
      _ ≤ 2^Nat.clog 2 (waveDegreeCoefficient C+1)*(2^ℓ)^8 :=
        Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := ℓ)).le 8)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hc : Nat.clog 2 (waveDegreeCoefficient C+1)≤Nat.clog 2 (waveDegreeCoefficient C+1)*ℓ :=
    Nat.le_mul_of_pos_right _ hℓ
  unfold waveWorkBits wavePrecisionCoefficient
  nlinarith only [hN,hclog,hc,hℓ]

theorem waveGrid_polylog {Q N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    waveGrid (8*Q) N≤waveGridCoefficient C*ℓ^8 := by
  have hw := waveWorkBits_polylog hℓ hQ hN
  have hp : ℓ≤ℓ^8 := le_self_pow₀ (by omega : 1≤ℓ) (by decide : (8:ℕ)≠0)
  have h1 : 1≤ℓ^8 := one_le_pow₀ (by omega)
  have hn := hN.trans (Nat.mul_le_mul_left C hp)
  have hwp := hw.trans (Nat.mul_le_mul_left _ hp)
  unfold waveGrid waveDegree waveGridCoefficient
  nlinarith only [hQ,hn,hwp,h1]

theorem tensorData_polylog (q : Fin 3→ℚ) {Q N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    (tensorData q Q N).length≤(waveDegreeCoefficient C)^3*ℓ^24 := by
  rw [tensorData_length]
  have h := Nat.pow_le_pow_left (waveDegree_polylog hℓ hQ hN) 3
  convert h using 1
  ring

theorem tensorBits_polylog (q : Fin 3→ℚ) {Q N C ℓ : ℕ} (hq : ∀ i, |q i|≤Q)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    (tensorBits q Q N).length≤tensorBitsCoefficient C*ℓ^25 := by
  have hd := Nat.pow_le_pow_left (waveDegree_polylog hℓ hQ hN) 3
  have hd' : (waveDegree (8*Q) N)^3≤(waveDegreeCoefficient C)^3*ℓ^24 := by
    convert hd using 1
    ring
  have hw := waveWorkBits_polylog hℓ hQ hN
  have h1 : 1≤ℓ^24 := one_le_pow₀ (by omega)
  have hD : (waveDegree (8*Q) N)^3+1≤((waveDegreeCoefficient C)^3+1)*ℓ^24 := by
    nlinarith only [hd',h1]
  have hP : 3*waveWorkBits (8*Q) N+17≤(3*wavePrecisionCoefficient C+17)*ℓ := by
    nlinarith only [hw,hℓ]
  calc
    _ ≤ 8*((waveDegree (8*Q) N)^3+1)*(3*waveWorkBits (8*Q) N+17) := tensorBits_length q Q N hq
    _ ≤ 8*(((waveDegreeCoefficient C)^3+1)*ℓ^24)*((3*wavePrecisionCoefficient C+17)*ℓ) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hD) hP
    _ = _ := by unfold tensorBitsCoefficient; ring

theorem tensorBits_paper_exponent (q : Fin 3→ℚ) {Q N C ℓ : ℕ} (hq : ∀ i, |q i|≤Q)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) :
    (tensorBits q Q N).length≤tensorBitsCoefficient C*ℓ^64 :=
  (tensorBits_polylog q hq hℓ hQ hN).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hℓ (by decide)))

#print axioms waveWorkBits_polylog
#print axioms tensorBits_polylog
#print axioms tensorBits_paper_exponent

end Maxwell.Continuum.Profile
