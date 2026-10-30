import Maxwell.Continuum.CalibrationRootGridCoefficientBounds

/-! Polynomial execution cost of the literal quadrature coefficient program. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option exponentiation.threshold 16384

theorem coefficientCost_polynomial (grid N B I : ℕ) :
    coefficientCost grid N B I≤2^13600*(grid^3+1)^57*(N+B+I+20)^224 := by
  generalize he : N+B+I+20=X
  generalize ha : grid^3+1=A
  have hA : 1≤A := by omega
  have hX : 1≤X := by omega
  have h14 : 1≤X^4 := one_le_pow₀ hX
  have hX4 : X≤X^4 := Nat.le_self_pow (by decide) _
  have hXA : X≤A*X^4 := hX4.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (X^4) hA)
  have hAA : A≤A*X^4 := by simpa only [mul_one] using Nat.mul_le_mul_left A h14
  have hprod : 1≤A*X^4 := one_le_mul_of_one_le_of_one_le hA h14
  have hw : loopWidth grid N (runtimeWidth B) I 0≤2^185*A*X^4 := by
    have hh := coefficientRawWidth_polynomial grid N B I
    rw [he,ha] at hh
    have hl : loopWidth grid N (runtimeWidth B) I 0≤coefficientRawWidth grid N B I := by
      unfold coefficientRawWidth;omega
    exact hl.trans hh
  have hlen : (grid^3).bits.length≤A := (bits_length_le_value (grid^3)).trans (by omega)
  have harg : N+loopWidth grid N (runtimeWidth B) I 0+(grid^3).bits.length+20≤2^187*A*X^4 := by
    have hn : N+20≤X := by omega
    rw [mul_assoc] at hw ⊢
    omega
  have hlast : loopWidth grid N (runtimeWidth B) I 0+3≤2^187*A*X^4 := by
    rw [mul_assoc] at hw ⊢
    omega
  have hAX : 1≤A^57*X^224 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hA) (one_le_pow₀ hX)
  have hX2 : X^2≤A^57*X^224 :=
    (Nat.pow_le_pow_right hX (by decide : 2≤224)).trans
      (by simpa only [one_mul] using Nat.mul_le_mul_right (X^224) (one_le_pow₀ hA (n:=57)))
  have hA2 : A^2≤A^57*X^224 :=
    (Nat.pow_le_pow_right hA (by decide : 2≤57)).trans
      (by simpa only [mul_one] using Nat.mul_le_mul_left (A^57) (one_le_pow₀ hX (n:=224)))
  have hA2X8 : A^2*X^8≤A^57*X^224 := Nat.mul_le_mul
    (Nat.pow_le_pow_right hA (by decide)) (Nat.pow_le_pow_right hX (by decide))
  have hstep : 2^3074*(N+loopWidth grid N (runtimeWidth B) I 0+(grid^3).bits.length+20)^56≤
      2^13546*A^56*X^224 := by
    calc
      _≤2^3074*(2^187*A*X^4)^56 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 56)
      _=_ := by ring
  have hsteps : grid^3*(2^3074*(N+loopWidth grid N (runtimeWidth B) I 0+(grid^3).bits.length+20)^56)≤
      2^13546*(A^57*X^224) := by
    calc
      _≤A*(2^13546*A^56*X^224) := Nat.mul_le_mul (by omega) hstep
      _=_ := by ring
  have hcount : (grid^3+1)*(13*(grid^3).bits.length+15)≤28*(A^57*X^224) := by
    rw [ha]
    calc
      _≤A*(28*A) := Nat.mul_le_mul_left _ (by omega)
      _=28*A^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ hA2
  have hfinish : 2^108*(loopWidth grid N (runtimeWidth B) I 0+3)^2≤2^482*(A^57*X^224) := by
    calc
      _≤2^108*(2^187*A*X^4)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlast 2)
      _=2^482*(A^2*X^8) := by ring
      _≤_ := Nat.mul_le_mul_left _ hA2X8
  have hstage : stageCost B+2*operationCost I+1≤2^103*(A^57*X^224) := by
    have hb : (B+2)^2≤X^2 := Nat.pow_le_pow_left (by omega) 2
    have hi : (I+3)^2≤X^2 := Nat.pow_le_pow_left (by omega) 2
    unfold stageCost operationCost
    omega
  unfold coefficientCost sumCost
  calc
    _≤(2^103+28+2^13546+2^482)*(A^57*X^224) := by
      omega
    _≤_ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ (by norm_num)

#print axioms coefficientCost_polynomial
end Maxwell.Continuum.RationalDataflow.RootGrid
