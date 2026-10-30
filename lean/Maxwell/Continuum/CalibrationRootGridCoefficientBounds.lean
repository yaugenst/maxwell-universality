import Maxwell.Continuum.CalibrationRootGridCoefficient

/-! Polynomial raw storage and execution bounds for literal product-grid
quadrature. The accumulator uses unreduced rational parts throughout. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option exponentiation.threshold 16384

theorem bits_length_le_value (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))

theorem coefficientRawWidth_polynomial (grid N B I : ℕ) :
    coefficientRawWidth grid N B I≤2^185*(grid^3+1)*(N+B+I+20)^4 := by
  generalize he : N+B+I+20=X
  have hX : 1≤X := by omega
  have hX4 : X≤X^4 := Nat.le_self_pow (by decide) _
  have h14 : 1≤X^4 := one_le_pow₀ hX
  have hdata : dataWidth (runtimeWidth B) I≤2^14*X := by
    unfold dataWidth naturalWidth runtimeWidth
    omega
  have hin : coefficientInputWidth (dataWidth (runtimeWidth B) I)≤2^24*X := by
    unfold coefficientInputWidth
    omega
  have harg : N+6*coefficientInputWidth (dataWidth (runtimeWidth B) I)+20≤2^27*X := by omega
  have hin4 : coefficientInputWidth (dataWidth (runtimeWidth B) I)≤2^24*X^4 :=
    hin.trans (Nat.mul_le_mul_left _ hX4)
  have hdata4 : dataWidth (runtimeWidth B) I≤2^14*X^4 :=
    hdata.trans (Nat.mul_le_mul_left _ hX4)
  have hsummand : summandWidth N (runtimeWidth B) I≤2^179*X^4 := by
    have hp : 2^70*(N+6*coefficientInputWidth (dataWidth (runtimeWidth B) I)+20)^4≤2^178*X^4 := by
      calc
        _≤2^70*(2^27*X)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 4)
        _=_ := by ring
    unfold summandWidth coefficientBankWidth RootProduct.workWidth RootProduct.coefficientWidth
    omega
  have hini : initialWidth N (runtimeWidth B) I≤2^180*X^4 := by
    have hb := bits_length_le_value N
    unfold initialWidth
    have hn4 : N≤X^4 := (show N≤X by omega).trans hX4
    omega
  have hstep : summandWidth N (runtimeWidth B) I+1≤2^180*X^4 := by
    omega
  have hloop : loopWidth grid N (runtimeWidth B) I 0≤2^180*(grid^3+1)*X^4 := by
    unfold loopWidth
    simp only [Nat.sub_zero]
    calc
      _≤2^180*X^4+grid^3*(2^180*X^4) := Nat.add_le_add hini (Nat.mul_le_mul_left _ hstep)
      _=_ := by ring
  have hprod : 1≤(grid^3+1)*X^4 := one_le_mul_of_one_le_of_one_le (by omega) h14
  unfold coefficientRawWidth
  rw [mul_assoc] at hloop ⊢
  omega


#print axioms coefficientRawWidth_polynomial
end Maxwell.Continuum.RationalDataflow.RootGrid
