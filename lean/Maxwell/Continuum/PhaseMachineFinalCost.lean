import Maxwell.Continuum.PhaseMachineFinalBank
import Maxwell.Continuum.PhaseMachineCost

/-! Uniform bounds including every temporary Machin/Taylor word. -/
namespace Maxwell.Continuum.PhaseMachine
set_option maxHeartbeats 2500000

theorem fullSeedWidth_polynomial (Q N W : ℕ) :
    fullSeedWidth Q N W+2≤2^38*(sizeParameter Q N W)^2 := by
  have hp := (Machin.wordWidth_bound (Calibration.phaseBits Q N)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (phaseBits_size Q N W) 2))
  have hW : W≤sizeParameter Q N W := by unfold sizeParameter;omega
  have hs : sizeParameter Q N W≤(sizeParameter Q N W)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ (by unfold sizeParameter;omega)
  unfold fullSeedWidth Machin.finalWidth
  unfold Machin.wordWidth at hp
  nlinarith only [hp,hW,hs,h1]

theorem fullWorkWidth_polynomial (Q N W : ℕ) :
    fullWorkWidth Q N W+3≤2^51*(sizeParameter Q N W)^2 := by
  have h := fullSeedWidth_polynomial Q N W
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ (by unfold sizeParameter;omega)
  unfold fullWorkWidth
  nlinarith only [h,h1]

theorem fullFinalWidth_polynomial (Q N W : ℕ) :
    fullFinalWidth Q N W≤2^66*(sizeParameter Q N W)^4 := by
  have ho := order_polynomial Q N W
  have hw := fullWorkWidth_polynomial Q N W
  have h1 : 1≤(sizeParameter Q N W)^2 := one_le_pow₀ (by unfold sizeParameter;omega)
  have hn : order Q N+1≤2^12*(sizeParameter Q N W)^2 := by omega
  have hs : fullWorkWidth Q N W+order Q N+3≤2^53*(sizeParameter Q N W)^2 := by
    nlinarith only [ho,hw,h1]
  have hm := Nat.mul_le_mul hn hs
  unfold fullFinalWidth RationalTaylor.width
  nlinarith only [hm,Nat.zero_le ((sizeParameter Q N W)^4)]

theorem fullCost_polynomial (Q N W : ℕ) :
    fullCost Q N W+1≤2^220*(sizeParameter Q N W)^14 := by
  have hp : 0<sizeParameter Q N W := by unfold sizeParameter;omega
  have h1 : 1≤(sizeParameter Q N W)^14 := one_le_pow₀ hp
  have h2 : (sizeParameter Q N W)^2≤(sizeParameter Q N W)^14 :=
    Nat.pow_le_pow_right hp (by decide)
  have h4 : (sizeParameter Q N W)^4≤(sizeParameter Q N W)^14 :=
    Nat.pow_le_pow_right hp (by decide)
  have h5 : (sizeParameter Q N W)^5≤(sizeParameter Q N W)^14 :=
    Nat.pow_le_pow_right hp (by decide)
  have hm : Machin.costBound (Calibration.phaseBits Q N)≤2^112*(sizeParameter Q N W)^14 :=
    (Machin.costBound_polynomial _).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left (phaseBits_size Q N W) 5).trans h5))
  have hw := fullWorkWidth_polynomial Q N W
  have hw' : fullWorkWidth Q N W+2≤2^51*(sizeParameter Q N W)^2 := by omega
  have hs : fullStageCost Q N W≤2^162*(sizeParameter Q N W)^14 := by
    have hh := Nat.mul_le_mul_left (2^60) (Nat.pow_le_pow_left hw' 2)
    unfold fullStageCost
    nlinarith only [hh,h4]
  have hg : 300*(2*fullWorkWidth Q N W+4)≤2^61*(sizeParameter Q N W)^14 := by
    nlinarith only [hw,h2]
  have ht : RationalTaylor.costBound (order Q N) (fullWorkWidth Q N W)≤
      2^206*(sizeParameter Q N W)^14 := by
    calc
      _ ≤ 2^44*(order Q N+2)^5*(fullWorkWidth Q N W+3)^2 := RationalTaylor.costBound_polynomial _ _
      _ ≤ 2^44*(2^12*(sizeParameter Q N W)^2)^5*(2^51*(sizeParameter Q N W)^2)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (order_polynomial Q N W) 5))
          (Nat.pow_le_pow_left hw 2)
      _ = _ := by ring
  unfold fullCost
  nlinarith only [hm,hs,hg,ht,h1]

#print axioms fullFinalWidth_polynomial
#print axioms fullCost_polynomial
end Maxwell.Continuum.PhaseMachine
