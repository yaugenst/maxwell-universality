import Maxwell.Continuum.RationalDataflowPower

/-! Polynomial bit work for the fixed runtime rational-power program. -/

namespace Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 1000000

theorem powerCost_polynomial (n W wordLength : ℕ) :
    powerCost n W wordLength≤2^106*(n+1)^3*(W+2)^2+(n+1)*(13*wordLength+15) := by
  have hwidth : powerWidth n W+3≤4*(n+1)*(W+2) := by
    unfold powerWidth
    nlinarith
  have hwidth' : powerWidth n W+2≤4*(n+1)*(W+2) := by omega
  have hsq := Nat.pow_le_pow_left hwidth 2
  have hsq' := Nat.pow_le_pow_left hwidth' 2
  have h1 : 1≤(n+1)^2*(W+2)^2 := Nat.succ_le_of_lt (by positivity)
  have hs : stageCost (powerWidth n W)≤2^104*(n+1)^2*(W+2)^2 := by
    unfold stageCost
    nlinarith only [hsq']
  have ho : operationCost (powerWidth n W)+1≤2^105*(n+1)^2*(W+2)^2 := by
    unfold operationCost
    nlinarith only [hsq,h1]
  have hm := Nat.mul_le_mul_left n ho
  unfold powerCost
  nlinarith only [hs,hm,Nat.zero_le ((n+1)^2*(W+2)^2)]

theorem powerCost_source_polynomial (n W wordLength ell C : ℕ) (hell : 1≤ell)
    (hn : n≤C*ell^2) (hW : W≤C*ell^6) (hword : wordLength≤C*ell) :
    powerCost n W wordLength≤(2^106*(C+1)^3*(C+2)^2+(C+1)*(13*C+15))*ell^18 := by
  have he2 : 1≤ell^2 := Nat.one_le_pow _ _ hell
  have he6 : 1≤ell^6 := Nat.one_le_pow _ _ hell
  have he18 : ell^3≤ell^18 := Nat.pow_le_pow_right hell (by decide)
  have hn' : n+1≤(C+1)*ell^2 := by nlinarith only [hn,he2]
  have hW' : W+2≤(C+2)*ell^6 := by nlinarith only [hW,he6]
  have hword' : 13*wordLength+15≤(13*C+15)*ell := by nlinarith only [hword,hell]
  have hm := Nat.mul_le_mul (Nat.pow_le_pow_left hn' 3) (Nat.pow_le_pow_left hW' 2)
  have ht := Nat.mul_le_mul hn' hword'
  have hs := Nat.mul_le_mul_left (2^106) hm
  have heq : ((C+1)*ell^2)^3*((C+2)*ell^6)^2=(C+1)^3*(C+2)^2*ell^18 := by ring
  rw [heq] at hs
  have ht' : (n+1)*(13*wordLength+15)≤(C+1)*(13*C+15)*ell^18 := by
    calc
      _ ≤ ((C+1)*ell^2)*((13*C+15)*ell) := ht
      _ = (C+1)*(13*C+15)*ell^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ he18
  have hp := powerCost_polynomial n W wordLength
  nlinarith only [hp,hs,ht']

#print axioms powerCost_source_polynomial

end Maxwell.Continuum.RationalDataflow
