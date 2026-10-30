import Maxwell.Continuum.FourierTensorGeneratedCoefficient
import Maxwell.Continuum.FourierTensorFactorCost

/-! Polynomial cost of the complete fixed alias traversal and canonical
tensor coefficient, including the unnormalized running sum. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow RationalTaylor RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

theorem accumulator_scale (n W X : ℕ) (hW : W ≤ X) (hX : 64 ≤ X) :
    aliasAccumulatorWidth n 0 W+22*W+26 ≤ 64*((n+1)*X) := by
  have hn := Nat.mul_le_mul_left n hW
  unfold aliasAccumulatorWidth
  simp only [Nat.sub_zero]
  nlinarith only [hW,hX,hn,Nat.zero_le n]

theorem termReturnCost_scale (A W R : ℕ) (hA : A+22*W+26 ≤ 64*R) (hR : 1 ≤ R) :
    termReturnCost A W ≤ 2^120*R^2 := by
  have h1 : A+22*W+22+3 ≤ 64*R := by omega
  have h2 : A+22*W+23+3 ≤ 64*R := by omega
  have p1 := Nat.pow_le_pow_left h1 2
  have p2 := Nat.pow_le_pow_left h2 2
  have hp : 1 ≤ R^2 := one_le_pow₀ hR
  unfold termReturnCost termCost operationCost
  nlinarith only [p1,p2,hp]

theorem aliasReadCost_scale (W k X : ℕ) (hk : k ≤ W) (hX : W+64 ≤ X) :
    aliasReadCost W k ≤ 2^40*X^2 := by
  have hs := Nat.pow_le_pow_left (by omega : W+11 ≤ X) 2
  have hpos : 1 ≤ X^2 := one_le_pow₀ (by omega : 1 ≤ X)
  have hx : X ≤ X^2 := Nat.le_self_pow (by decide) X
  change 21*k+25+(5*(2^30*(W+11)^2)+1) ≤ _
  omega

def coefficientTimeCoefficient : ℕ := axesTimeCoefficient+2^140

theorem summedCoefficientCost_le (a T : ℕ) :
    2^96*T+(32*T+(2^40*T+(a*T+2^120*T)))+2^112*T ≤ (a+2^140)*T := by
  rw [Nat.add_mul]
  omega

theorem scaled_power_step (n c X : ℕ) :
    (n+1)*(c*((n+1)^2*X))=c*((n+1)^3*X) := by ring

theorem generatedCoefficientCost_polynomial (Q N n W k : ℕ) (j : Fin 3→ℕ)
    (hk : k ≤ W) (hj : ∀i,(j i).bits.length ≤ W) :
    generatedCoefficientCost Q N n W k j ≤
      coefficientTimeCoefficient*(n+1)^3*(Q+N+W+64)^240 := by
  let X := Q+N+W+64
  let R := (n+1)*X
  let A := aliasAccumulatorWidth n 0 W
  have hX : W+64 ≤ X := by dsimp [X];omega
  have hW : W ≤ X := by omega
  have h64 : 64 ≤ X := by omega
  have h1 : 1 ≤ X := by omega
  have hR : 1 ≤ R := Nat.mul_le_mul (by omega : 1 ≤ n+1) (by omega : 1 ≤ X)
  have hA : A+22*W+26 ≤ 64*R := accumulator_scale n W X hW h64
  have ht := termReturnCost_scale A W R hA hR
  have hr := aliasReadCost_scale W k X hk hX
  have ha := axesCost_polynomial Q N W j hj
  have hstage : stageCost W ≤ 2^96*X^2 := by
    clear * -hX
    unfold stageCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hop : operationCost A ≤ 2^112*R^2 := by
    clear * -hA
    have hs := Nat.pow_le_pow_left (by omega : A+3 ≤ 64*R) 2
    unfold operationCost
    nlinarith only [hs]
  have hcount : (n+1)*(13*k+15) ≤ 32*(n+1)*X := by
    clear * -hk hX
    have hh : 13*k+15 ≤ 32*X := by omega
    exact (Nat.mul_le_mul_left (n+1) hh).trans_eq (by ring)
  have hx2 : X^2 ≤ X^240 := Nat.pow_le_pow_right h1 (by decide)
  have hx : X ≤ X^240 := Nat.le_self_pow (by decide) X
  have hn1 : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by decide) (n+1)
  have hn2 : (n+1)^2 ≤ (n+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn0 : 1 ≤ (n+1)^3 := one_le_pow₀ (by omega)
  have hsq3 : X^2 ≤ (n+1)^3*X^240 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hn0 hx2
  have hsq2 : X^2 ≤ (n+1)^2*X^240 := by
    have hnp : 1 ≤ (n+1)^2 := one_le_pow₀ (by omega)
    simpa only [Nat.one_mul] using Nat.mul_le_mul hnp hx2
  have hs' : stageCost W ≤ 2^96*((n+1)^3*X^240) :=
    hstage.trans (Nat.mul_le_mul_left _ hsq3)
  have hr' : aliasReadCost W k ≤ 2^40*((n+1)^2*X^240) :=
    hr.trans (Nat.mul_le_mul_left _ hsq2)
  have ht' : termReturnCost A W ≤ 2^120*((n+1)^2*X^240) := by
    apply ht.trans
    dsimp [R]
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hx2)
  have hop' : operationCost A ≤ 2^112*((n+1)^3*X^240) := by
    apply hop.trans
    dsimp [R]
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hn2 hx2)
  have hc' : (n+1)*(13*k+15) ≤ 32*((n+1)^3*X^240) :=
    hcount.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 32 (Nat.mul_le_mul hn1 hx))
  have hab : n*axesCost Q N W j ≤ axesTimeCoefficient*((n+1)^3*X^240) := by
    calc
      _ ≤ n*(axesTimeCoefficient*X^240) := Nat.mul_le_mul_left n ha
      _ = axesTimeCoefficient*(n*X^240) := by rw [Nat.mul_left_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ((by omega : n ≤ n+1).trans hn1))
  have hnr : n*aliasReadCost W k ≤ 2^40*((n+1)^3*X^240) := by
    calc
      _ ≤ (n+1)*(2^40*((n+1)^2*X^240)) := Nat.mul_le_mul (by omega) hr'
      _ = _ := scaled_power_step n _ _
  have hnt : n*termReturnCost A W ≤ 2^120*((n+1)^3*X^240) := by
    calc
      _ ≤ (n+1)*(2^120*((n+1)^2*X^240)) := Nat.mul_le_mul (by omega) ht'
      _ = _ := scaled_power_step n _ _
  change stageCost W+((n+1)*(13*k+15)+n*(aliasReadCost W k+
    (axesCost Q N W j+termReturnCost A W)))+operationCost A ≤ _
  rw [Nat.mul_add n (aliasReadCost W k) (axesCost Q N W j+termReturnCost A W),
    Nat.mul_add n (axesCost Q N W j) (termReturnCost A W)]
  calc
    _ ≤ 2^96*((n+1)^3*X^240)+(32*((n+1)^3*X^240)+
      (2^40*((n+1)^3*X^240)+(axesTimeCoefficient*((n+1)^3*X^240)+
      2^120*((n+1)^3*X^240))))+2^112*((n+1)^3*X^240) :=
      Nat.add_le_add (Nat.add_le_add hs' (Nat.add_le_add hc'
        (Nat.add_le_add hnr (Nat.add_le_add hab hnt)))) hop'
    _ ≤ coefficientTimeCoefficient*((n+1)^3*X^240) :=
      summedCoefficientCost_le axesTimeCoefficient ((n+1)^3*X^240)
    _ = _ := (Nat.mul_assoc coefficientTimeCoefficient ((n+1)^3) (X^240)).symm

#print axioms generatedCoefficientCost_polynomial
end Maxwell.Continuum.Profile.WaveMachine.Runtime
