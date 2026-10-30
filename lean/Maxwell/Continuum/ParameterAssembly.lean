import Maxwell.Continuum.MasterConstants

/-! Scalar consequences of the literal first spacing test for the dark
inverse and the mixed-block correction in the finite auxiliary assembly. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

/-- The first test has enough margin to control the entire offsite block. -/
theorem first_spacing_mixed_small {L ζ ε : ℝ} (hL : Ls ≤ L) (hζ : 0 ≤ ζ)
    (hε : ε ≤ 1) (htest : Cs^4*L^12*ζ ≤ ε/(2 : ℝ)^24) :
    Cs*L^5*ζ ≤ 1/(2 : ℝ)^512 := by
  have hL1 := length_ge_one hL
  have hL0 := length_pos hL
  have hCs := Cs_pos
  have hfac : (2 : ℝ)^512 ≤ Cs^3*L^7 :=
    (H1_constant_le_Cs.trans (le_self_pow₀ Cs_ge_one (by decide : (3 : ℕ) ≠ 0))).trans
      (le_mul_of_one_le_right (pow_nonneg hCs.le 3) (one_le_pow₀ hL1))
  have hp := mul_le_mul_of_nonneg_right hfac
    (mul_nonneg (mul_nonneg hCs.le (pow_nonneg hL0.le 5)) hζ)
  have he : Cs^3*L^7*(Cs*L^5*ζ) = Cs^4*L^12*ζ := by ring
  rw [he] at hp
  have hb : ε/(2 : ℝ)^24 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact hε.trans (one_le_pow₀ (by norm_num))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^512)).mpr
  simpa only [mul_comm] using hp.trans (htest.trans hb)

/-- Actual numerical budgets imply all three scalar hypotheses used in
complement inversion and the mixed Schur correction. -/
theorem assembly_scalar_budgets {L ζ ε c tail dt : ℝ} (hL : Ls ≤ L) (hζ : 0 ≤ ζ)
    (hε : ε ≤ 1) (htest : Cs^4*L^12*ζ ≤ ε/(2 : ℝ)^24)
    (hc : c ≤ (1/(2 : ℝ)^196)*L^2+ζ^2)
    (htail : tail ≤ ζ^2/4) (hdt : dt ≤ ζ^2/(2 : ℝ)^20) :
    c+64*(Cs*L^5)*ζ+tail+dt ≤ ((1/(2 : ℝ)^192)*L^2)/2 ∧
    64*(Cs*L^5)*ζ+tail+dt ≤ 128*(Cs*L^5)*ζ ∧
    (64*(Cs*L^5)*ζ+tail+dt)*((2 : ℝ)^194*L⁻¹^2) ≤ 1 := by
  have hL1 := length_ge_one hL
  have hL0 := length_pos hL
  have hCs := Cs_pos
  have hA : 1 ≤ Cs*L^5 := one_le_mul_of_one_le_of_one_le Cs_ge_one (one_le_pow₀ hL1)
  have hx := first_spacing_mixed_small hL hζ hε htest
  let x := Cs*L^5*ζ
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg hCs.le (pow_nonneg hL0.le 5)) hζ
  have hxsmall : x ≤ 1/(2 : ℝ)^512 := hx
  have hzX : ζ ≤ x := by
    dsimp only [x]
    exact le_mul_of_one_le_left hζ hA
  have hz1 : ζ ≤ 1 := hzX.trans (hxsmall.trans (by norm_num))
  have hzsq : ζ^2 ≤ ζ := by nlinarith
  have hts : tail ≤ x := (htail.trans (by nlinarith)).trans hzX
  have hds : dt ≤ x := (hdt.trans (by nlinarith)).trans hzX
  have hm : 64*(Cs*L^5)*ζ+tail+dt ≤ 66*x := by dsimp only [x] at *; linarith
  have hsq : 1 ≤ L^2 := one_le_pow₀ hL1
  have hnum : (67 : ℝ)/(2 : ℝ)^512 ≤ 1/(2 : ℝ)^193-1/(2 : ℝ)^196 := by norm_num
  have hs67 : 67*x ≤ (1/(2 : ℝ)^193-1/(2 : ℝ)^196)*L^2 :=
    (mul_le_mul_of_nonneg_left hxsmall (by norm_num)).trans
      (by calc
        67*(1/(2 : ℝ)^512) = 67/(2 : ℝ)^512 := by ring
        _ ≤ 1/(2 : ℝ)^193-1/(2 : ℝ)^196 := hnum
        _ ≤ _ := le_mul_of_one_le_right (by norm_num) hsq)
  refine ⟨?_, ?_, ?_⟩
  · have hc' : c ≤ (1/(2 : ℝ)^196)*L^2+x := hc.trans (by linarith)
    have hp : ((1/(2 : ℝ)^192)*L^2)/2 = (1/(2 : ℝ)^193)*L^2 := by norm_num; ring
    rw [hp]
    linarith
  · exact hm.trans (by nlinarith)
  · have hi : L⁻¹^2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
    have hh : 0 ≤ (2 : ℝ)^194*L⁻¹^2 := by positivity
    calc
      _ ≤ (66*x)*((2 : ℝ)^194*L⁻¹^2) := mul_le_mul_of_nonneg_right hm hh
      _ ≤ (66*(1/(2 : ℝ)^512))*((2 : ℝ)^194*1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hxsmall (by norm_num))
          (mul_le_mul_of_nonneg_left hi (by positivity)) hh (by positivity)
      _ ≤ 1 := by norm_num

#print axioms first_spacing_mixed_small
#print axioms assembly_scalar_budgets

end Maxwell.Continuum.Parameters
