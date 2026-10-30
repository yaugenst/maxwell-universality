import Maxwell.Continuum.ParameterAssembly

/-! The literal second spacing test pays for all mediator diagonal shifts. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

theorem second_test_budget {L ζ α K ε : ℝ} (_hL : Ls ≤ L) (hα : 0 < α)
    (hK : 1 ≤ K) (hε : ε ≤ 1)
    (htest : Cs^4*L^12*ζ^2 ≤ α*ε/((2 : ℝ)^24*K)) :
    Cs^4*L^12*ζ^2 ≤ α := by
  have hden : 1 ≤ (2 : ℝ)^24*K :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hK
  have hquot : ε/((2 : ℝ)^24*K) ≤ 1 :=
    (div_le_one (zero_lt_one.trans_le hden)).mpr (hε.trans hden)
  have hmul := mul_le_mul_of_nonneg_left hquot hα.le
  rw [mul_one, ← mul_div_assoc] at hmul
  exact htest.trans hmul

theorem second_test_square_le {L ζ α K ε : ℝ} (hL : Ls ≤ L) (hα : 0 < α)
    (hK : 1 ≤ K) (hε : ε ≤ 1)
    (htest : Cs^4*L^12*ζ^2 ≤ α*ε/((2 : ℝ)^24*K)) : ζ^2 ≤ α := by
  have hfactor : 1 ≤ Cs^4*L^12 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ Cs_ge_one) (one_le_pow₀ (length_ge_one hL))
  exact (le_mul_of_one_le_left (sq_nonneg ζ) hfactor).trans
    (second_test_budget hL hα hK hε htest)

theorem second_test_zeta {L ζ α K ε : ℝ} (hL : Ls ≤ L) (hα : 0 < α)
    (hK : 1 ≤ K) (hε : ε ≤ 1)
    (htest : Cs^4*L^12*ζ^2 ≤ α*ε/((2 : ℝ)^24*K)) : ζ^2/16 ≤ α :=
  (div_le_self (sq_nonneg ζ) (by norm_num)).trans (second_test_square_le hL hα hK hε htest)

theorem mediator_square_budget {L ζ α K ε β : ℝ} (hL : Ls ≤ L) (hα : 0 < α)
    (hK : 1 ≤ K) (hε : ε ≤ 1)
    (htest : Cs^4*L^12*ζ^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hβ : |β| ≤ 2*Cs*L^5*ζ) : β^2/α ≤ (1/(2 : ℝ)^196)*L^2 := by
  have hL1 := length_ge_one hL
  have hL0 := length_pos hL
  have hCs := Cs_pos
  have hfac : (2 : ℝ)^198 ≤ Cs^2*L^2 :=
    ((by norm_num : (2 : ℝ)^198 ≤ 2^512).trans H1_constant_le_Cs).trans
      ((le_self_pow₀ Cs_ge_one (by decide : (2 : ℕ) ≠ 0)).trans
        (le_mul_of_one_le_right (sq_nonneg Cs) (one_le_pow₀ hL1)))
  have hbsq : β^2 ≤ 4*Cs^2*L^10*ζ^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg β) ((abs_nonneg β).trans hβ)).mpr hβ
    rw [sq_abs] at hh
    convert hh using 1
    ring
  have hprod := mul_le_mul_of_nonneg_right hfac
    (show 0 ≤ Cs^2*L^10*ζ^2 by positivity)
  have he : Cs^2*L^2*(Cs^2*L^10*ζ^2) = Cs^4*L^12*ζ^2 := by ring
  rw [he] at hprod
  have htest' := second_test_budget hL hα hK hε htest
  have hnum : (2 : ℝ)^198 = (2 : ℝ)^196*4 := by norm_num
  rw [hnum] at hprod
  have hsmall : β^2 ≤ (1/(2 : ℝ)^196)*α := by
    rw [show (1/(2 : ℝ)^196)*α = α/(2 : ℝ)^196 by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^196)).mpr
    have hb := mul_le_mul_of_nonneg_left hbsq (by positivity : (0 : ℝ) ≤ 2^196)
    calc
      β^2*2^196 = 2^196*β^2 := by ring
      _ ≤ 2^196*(4*Cs^2*L^10*ζ^2) := hb
      _ = 2^196*4*(Cs^2*L^10*ζ^2) := by ring
      _ ≤ _ := hprod.trans htest'
  have hdiv := (div_le_iff₀ hα).mpr hsmall
  exact hdiv.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1))

theorem terminal_budget {L : ℝ} (hL : Ls ≤ L) : 6 ≤ (1/(2 : ℝ)^196)*L^2 := by
  have hl : (2 : ℝ)^100 ≤ L :=
    (power_le_Ls (by have := exponent_large; omega)).trans hL
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2^100) hl 2
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1/2^196)
  exact (by norm_num : (6 : ℝ) ≤ (1/2^196)*(2^100)^2).trans hm

#print axioms mediator_square_budget
#print axioms terminal_budget
#print axioms second_test_zeta

end Maxwell.Continuum.Parameters
