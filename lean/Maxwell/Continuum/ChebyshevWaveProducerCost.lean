import Maxwell.Continuum.ChebyshevWaveProducer

/-! Explicit polynomial time for the fixed producer, including setup. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

def producerTimeCoefficient : ℕ := 2^180+2^110+2^7200*2^9*(2^15)^15*(2^137)^56

theorem cache_monomial (a b c d X : ℕ) :
    a*(b*X)*(c*X)^15*(d*X^4)^56=(a*b*c^15*d^56)*X^240 := by ring

theorem producerBound_polynomial (Q N W : ℕ) :
    producerBound Q N W≤producerTimeCoefficient*(Q+N+W+64)^240 := by
  let X := Q+N+W+64
  let P := waveWorkBits (8*Q) N
  let G := waveGrid (8*Q) N
  let D := waveDegree (8*Q) N
  let B := producerWidth Q N W
  have hX : 1≤X := by dsimp [X];omega
  have hQ : Q≤X := by dsimp [X];omega
  have hN : N≤X := by dsimp [X];omega
  have hW : W+4≤X := by dsimp [X];omega
  have h64 : 64≤X := by dsimp [X];omega
  have hD : D≤2^8*X := by dsimp [D,waveDegree,X];omega
  have hP : P≤2^9*X := by
    have hb := Machin.Runtime.nat_bits_le_self D
    change (waveDegree (8*Q) N).bits.length≤D at hb
    dsimp [P]
    rw [workBits_eq]
    omega
  have hG : G≤2^14*X := by
    change D+16*(8*Q+P+16)+1≤_
    omega
  have hB : B≤2^30*X := by
    have hw : dimensionWidth W≤2^28*X := by
      unfold dimensionWidth
      exact Nat.mul_le_mul_left _ (by omega)
    change dimensionWidth W+P+W+8≤_
    omega
  have hS : smallScale Q P B≤2^34*X := by
    have hb := Machin.Runtime.nat_bits_le_self Q
    unfold smallScale
    omega
  have hx4 : X≤X^4 := Nat.le_self_pow (by decide) X
  have hT : frequencyScale Q P B≤2^137*X^4 := by
    have hs := Nat.pow_le_pow_left hS 4
    unfold frequencyScale
    nlinarith only [hs,hQ,hx4,Nat.zero_le (X^4)]
  have hD' : D+2≤2^9*X := by omega
  have hG' : G+1≤2^15*X := by omega
  have hcache : cacheBound Q N (D+1) B≤(2^7200*2^9*(2^15)^15*(2^137)^56)*X^240 := by
    change 2^7200*(D+1+1)*(G+1)^15*(frequencyScale Q P B)^56≤_
    calc
      _≤2^7200*(2^9*X)*(2^15*X)^15*(2^137*X^4)^56 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD')
          (Nat.pow_le_pow_left hG' 15)) (Nat.pow_le_pow_left hT 56)
      _=_ := cache_monomial _ _ _ _ _
  have hx2 : X^2≤X^240 := Nat.pow_le_pow_right hX (by decide)
  have hsmall : W+P+4≤2^10*X := by omega
  have hsetup : 2^160*(W+P+4)^2≤2^180*X^240 := by
    calc
      _≤2^160*(2^10*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 2)
      _=2^180*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ hx2
  have hbase : baseCost W G≤2^110*X^240 := by
    have hg := (Machin.Runtime.nat_bits_le_self G).trans hG
    have hx : X≤X^240 := Nat.le_self_pow (by decide) X
    have hone : 1≤X^240 := one_le_pow₀ hX
    have hop : operationCost (W+1)≤2^100*X^240 := by
      unfold operationCost
      exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hW 2).trans hx2)
    have hg' := hg.trans (Nat.mul_le_mul_left (2^14) hx)
    unfold baseCost
    omega
  change 2^160*(W+P+4)^2+baseCost W G+cacheBound Q N (D+1) B≤_
  calc
    _≤2^180*X^240+2^110*X^240+(2^7200*2^9*(2^15)^15*(2^137)^56)*X^240 :=
      Nat.add_le_add (Nat.add_le_add hsetup hbase) hcache
    _=producerTimeCoefficient*X^240 := by simp only [producerTimeCoefficient,Nat.add_mul]

def producerCoefficient (C : ℕ) : ℕ := producerTimeCoefficient*(3*C+64)^240

theorem producerBound_polylog {Q N W C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) (hW : W≤C*ℓ) :
    producerBound Q N W≤producerCoefficient C*ℓ^1920 := by
  have hp : ℓ≤ℓ^8 := Nat.le_self_pow (by decide) ℓ
  have hone : 1≤ℓ^8 := one_le_pow₀ hℓ
  have hn := hN.trans (Nat.mul_le_mul_left C hp)
  have hw := hW.trans (Nat.mul_le_mul_left C hp)
  have hx : Q+N+W+64≤(3*C+64)*ℓ^8 := by nlinarith only [hQ,hn,hw,hone]
  calc
    _≤producerTimeCoefficient*(Q+N+W+64)^240 := producerBound_polynomial Q N W
    _≤producerTimeCoefficient*((3*C+64)*ℓ^8)^240 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 240)
    _=producerCoefficient C*ℓ^1920 := by
      rw [mul_pow,←pow_mul]
      simp only [producerCoefficient,Nat.mul_assoc,show 8*240=1920 by decide]

#print axioms producerBound_polynomial
#print axioms producerBound_polylog
end Maxwell.Continuum.Profile.WaveMachine.Runtime
