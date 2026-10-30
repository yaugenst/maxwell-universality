import Maxwell.Continuum.ParameterAssembly

/-! The literal bright Schur error budget is paid by the squared-spacing
allowance, including the complementary inverse correction. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

private theorem bright_coefficient_budget {C L : ℝ} (hC : (2 : ℝ)^512 ≤ C) (hL : 1 ≤ L) :
    2+256*(C*L^5)+(2 : ℝ)^208*C^2*L^8 ≤ C^4*L^12 := by
  have hC1 : 1 ≤ C := (by norm_num : (1 : ℝ) ≤ 2^512).trans hC
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hC10 : (2 : ℝ)^10 ≤ C^3*L^7 :=
    ((by norm_num : (2 : ℝ)^10 ≤ 2^512).trans hC).trans
      ((le_self_pow₀ hC1 (by decide : (3 : ℕ) ≠ 0)).trans
        (le_mul_of_one_le_right (pow_nonneg hC0.le 3) (one_le_pow₀ hL)))
  have hC210 : (2 : ℝ)^210 ≤ C^2*L^4 :=
    ((by norm_num : (2 : ℝ)^210 ≤ 2^512).trans hC).trans
      ((le_self_pow₀ hC1 (by decide : (2 : ℕ) ≠ 0)).trans
        (le_mul_of_one_le_right (pow_nonneg hC0.le 2) (one_le_pow₀ hL)))
  have hbase : 8 ≤ C^4*L^12 :=
    ((by norm_num : (8 : ℝ) ≤ 2^512).trans hC).trans
      ((le_self_pow₀ hC1 (by decide : (4 : ℕ) ≠ 0)).trans
        (le_mul_of_one_le_right (pow_nonneg hC0.le 4) (one_le_pow₀ hL)))
  have hA := mul_le_mul_of_nonneg_right hC10 (show 0 ≤ C*L^5 by positivity)
  have hB := mul_le_mul_of_nonneg_right hC210 (show 0 ≤ C^2*L^8 by positivity)
  have heA : C^3*L^7*(C*L^5) = C^4*L^12 := by ring
  have heB : C^2*L^4*(C^2*L^8) = C^4*L^12 := by ring
  rw [heA] at hA
  rw [heB] at hB
  norm_num only [show (2 : ℝ)^10 = 1024 by norm_num] at hA
  have hn : (2 : ℝ)^210 = 4*(2 : ℝ)^208 := by norm_num
  rw [hn] at hB
  nlinarith

theorem assembly_bright_error {L ζ tail dt : ℝ} (hL : Ls ≤ L)
    (htail : tail ≤ ζ^2/4) (hdt : dt ≤ ζ^2/(2 : ℝ)^20) :
    ζ^2+3*(ζ^2/16)+(256*(Cs*L^5)*ζ^2+tail)+dt+
      (128*(Cs*L^5)*ζ)^2*((2 : ℝ)^194*L⁻¹^2) ≤ Cs^4*L^12*ζ^2 := by
  have hL0 := length_pos hL
  have hCs := Cs_pos
  have hcoef := bright_coefficient_budget H1_constant_le_Cs (length_ge_one hL)
  have hm : (128*(Cs*L^5)*ζ)^2*((2 : ℝ)^194*L⁻¹^2) =
      (2 : ℝ)^208*Cs^2*L^8*ζ^2 := by
    field_simp
    ring
  rw [hm]
  have hb := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ζ)
  have hsmall : ζ^2+3*(ζ^2/16)+tail+dt ≤ 2*ζ^2 := by
    nlinarith [sq_nonneg ζ]
  nlinarith

#print axioms assembly_bright_error

end Maxwell.Continuum.Parameters
