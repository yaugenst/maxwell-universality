import Maxwell.Continuum.GlueMachineProgram

/-! Polynomial bit cost and unreduced output width for the literal glue primitive. -/

namespace Maxwell.Continuum.GlueMachine
set_option maxHeartbeats 1000000

def sizeParameter (N W : ℕ) : ℕ := N+W+10

theorem seedWidth_polynomial (N W : ℕ) : seedWidth N W+2≤sizeParameter N W := by
  unfold seedWidth sizeParameter
  omega

theorem preparedWidth_polynomial (N W : ℕ) : preparedWidth N W+3≤2^5*sizeParameter N W := by
  have h := seedWidth_polynomial N W
  have h1 : 1≤sizeParameter N W := by unfold sizeParameter; omega
  unfold preparedWidth
  nlinarith only [h,h1]

theorem order_polynomial (N W : ℕ) : order N+2≤2^5*(sizeParameter N W)^2 := by
  have hn : N+1≤sizeParameter N W := by unfold sizeParameter; omega
  have hs2 : sizeParameter N W≤(sizeParameter N W)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(sizeParameter N W)^2 := one_le_pow₀ (by unfold sizeParameter; omega)
  have hn2 := Nat.pow_le_pow_left hn 2
  have ho : order N+2≤Calibration.taylorOrder (N+1) N+2 := by unfold order; omega
  unfold Calibration.taylorOrder Calibration.taylorHalfOrder at ho
  nlinarith only [ho,hn2,hn,hs2,h1]

theorem resultWidth_polynomial (N W : ℕ) : resultWidth N W≤2^16*(sizeParameter N W)^4 := by
  have ho := order_polynomial N W
  have hw := preparedWidth_polynomial N W
  have hs2 : sizeParameter N W≤(sizeParameter N W)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(sizeParameter N W)^4 := one_le_pow₀ (by unfold sizeParameter; omega)
  have hprod : (order N+1)*(preparedWidth N W+order N+3)≤
      (2^5*(sizeParameter N W)^2)*(2^6*(sizeParameter N W)^2) := by
    exact Nat.mul_le_mul (by omega) (by nlinarith only [ho,hw,hs2])
  unfold resultWidth RationalTaylor.width
  nlinarith only [hprod,h1]

theorem costBound_polynomial (N W : ℕ) : costBound N W≤2^84*(sizeParameter N W)^12 := by
  have hpos : 0<sizeParameter N W := by unfold sizeParameter; omega
  have h1 : 1≤(sizeParameter N W)^12 := one_le_pow₀ (by omega)
  have h2 : (sizeParameter N W)^2≤(sizeParameter N W)^12 := Nat.pow_le_pow_right hpos (by decide)
  have hs : stageCost N W≤2^50*(sizeParameter N W)^12 := by
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (seedWidth_polynomial N W) 2)).trans
      (Nat.mul_le_mul_left _ h2)
  have hc : comparisonCost N W≤2^25*(sizeParameter N W)^12 := by
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (seedWidth_polynomial N W) 2)).trans
      (Nat.mul_le_mul_left _ h2)
  have ht : RationalTaylor.costBound (order N) (preparedWidth N W)≤2^79*(sizeParameter N W)^12 := by
    calc
      _ ≤ 2^44*(order N+2)^5*(preparedWidth N W+3)^2 := RationalTaylor.costBound_polynomial _ _
      _ ≤ 2^44*(2^5*(sizeParameter N W)^2)^5*(2^5*sizeParameter N W)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (order_polynomial N W) 5))
          (Nat.pow_le_pow_left (preparedWidth_polynomial N W) 2)
      _ = _ := by ring
  unfold costBound
  nlinarith only [hs,hc,ht,h1]

#print axioms resultWidth_polynomial
#print axioms costBound_polynomial

end Maxwell.Continuum.GlueMachine
