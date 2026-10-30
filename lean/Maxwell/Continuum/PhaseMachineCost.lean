import Maxwell.Continuum.PhaseMachineProgram

/-! A polynomial bit-instruction bound for the actual composed phase program. -/

namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 1500000

def sizeParameter (Q N W : ℕ) : ℕ := Q+N+W+10

theorem phaseBits_size (Q N W : ℕ) : Calibration.phaseBits Q N+1≤sizeParameter Q N W := by
  have h : Nat.clog 2 (Q+1)≤Q+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := Q+1)).le
  unfold Calibration.phaseBits sizeParameter
  omega

theorem seedWidth_polynomial (Q N W : ℕ) :
    seedWidth Q N W+2≤2^14*(sizeParameter Q N W)^2 := by
  have hs : 1≤sizeParameter Q N W := by unfold sizeParameter; omega
  have hs2 : sizeParameter Q N W≤(sizeParameter Q N W)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ hs
  have hw : W≤sizeParameter Q N W := by unfold sizeParameter; omega
  have hp := (Machin.wordWidth_bound (Calibration.phaseBits Q N)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (phaseBits_size Q N W) 2))
  unfold seedWidth
  nlinarith only [hp,hs2,h1,hw]

theorem preparedWidth_polynomial (Q N W : ℕ) :
    preparedWidth Q N W+3≤2^24*(sizeParameter Q N W)^2 := by
  have h := seedWidth_polynomial Q N W
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ (by unfold sizeParameter; omega)
  unfold preparedWidth
  nlinarith only [h,h1]

theorem order_polynomial (Q N W : ℕ) :
    order Q N+2≤2^12*(sizeParameter Q N W)^2 := by
  have hq : Q+1≤sizeParameter Q N W := by unfold sizeParameter; omega
  have hn : N≤sizeParameter Q N W := by unfold sizeParameter; omega
  have hs2 : sizeParameter Q N W≤(sizeParameter Q N W)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ (by unfold sizeParameter; omega)
  have hq2 := Nat.pow_le_pow_left hq 2
  have ho : order Q N+2≤Calibration.taylorOrder (10*(Q+1)) (N+3)+2 := by unfold order; omega
  unfold Calibration.taylorOrder Calibration.taylorHalfOrder at ho
  nlinarith only [ho,hq2,hn,hs2,h1]

theorem costBound_polynomial (Q N W : ℕ) :
    costBound Q N W+1≤2^160*(sizeParameter Q N W)^14 := by
  have hpos : 0<sizeParameter Q N W := by unfold sizeParameter; omega
  have h1 : 1≤(sizeParameter Q N W)^14 := one_le_pow₀ (by omega)
  have hp5 : (sizeParameter Q N W)^5≤(sizeParameter Q N W)^14 := Nat.pow_le_pow_right hpos (by decide)
  have hp4 : (sizeParameter Q N W)^4≤(sizeParameter Q N W)^14 := Nat.pow_le_pow_right hpos (by decide)
  have hp2 : (sizeParameter Q N W)^2≤(sizeParameter Q N W)^14 := Nat.pow_le_pow_right hpos (by decide)
  have hm : Machin.costBound (Calibration.phaseBits Q N)≤2^112*(sizeParameter Q N W)^14 := by
    apply (Machin.costBound_polynomial _).trans
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (phaseBits_size Q N W) 5).trans hp5)
  have hs : stageCost Q N W≤2^78*(sizeParameter Q N W)^14 := by
    calc
      _ ≤ 2^50*(2^14*(sizeParameter Q N W)^2)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (seedWidth_polynomial Q N W) 2)
      _ = 2^78*(sizeParameter Q N W)^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp4
  have hmag : 300*(2*Machin.wordWidth (Calibration.phaseBits Q N)+4)≤2^24*(sizeParameter Q N W)^14 := by
    have hw := (Machin.wordWidth_bound (Calibration.phaseBits Q N)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (phaseBits_size Q N W) 2))
    nlinarith only [hw,hp2,h1]
  have ht : RationalTaylor.costBound (order Q N) (preparedWidth Q N W)≤2^152*(sizeParameter Q N W)^14 := by
    calc
      _ ≤ 2^44*(order Q N+2)^5*(preparedWidth Q N W+3)^2 := RationalTaylor.costBound_polynomial _ _
      _ ≤ 2^44*(2^12*(sizeParameter Q N W)^2)^5*(2^24*(sizeParameter Q N W)^2)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (order_polynomial Q N W) 5))
          (Nat.pow_le_pow_left (preparedWidth_polynomial Q N W) 2)
      _ = _ := by ring
  unfold costBound
  nlinarith only [hm,hs,hmag,ht,h1]

theorem costBound_polylog {Q N W C ℓ : ℕ} (hℓ : 0<ℓ)
    (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ^8) (hW : W≤C*ℓ^8) :
    costBound Q N W+1≤(2^160*(3*C+10)^14)*ℓ^112 := by
  have h1 : 1≤ℓ^8 := one_le_pow₀ (by omega)
  have hs : sizeParameter Q N W≤(3*C+10)*ℓ^8 := by
    unfold sizeParameter
    nlinarith only [hQ,hN,hW,h1]
  calc
    _ ≤ 2^160*(sizeParameter Q N W)^14 := costBound_polynomial Q N W
    _ ≤ 2^160*((3*C+10)*ℓ^8)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 14)
    _ = _ := by ring

#print axioms costBound_polynomial
#print axioms costBound_polylog

end Maxwell.Continuum.PhaseMachine
