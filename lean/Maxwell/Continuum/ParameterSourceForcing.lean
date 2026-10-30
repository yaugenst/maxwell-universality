import Maxwell.Continuum.ParameterAssembly

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048

theorem source_forcing_budget {L ζ ε : ℝ} (hL : Ls ≤ L) (hζ : 0 ≤ ζ)
    (htest : Cs^4*L^12*ζ ≤ ε/(2 : ℝ)^24) :
    ((2 : ℝ)^128*L⁻¹^2)*(128*Cs*L^5*ζ) ≤ ε/(2 : ℝ)^24 := by
  have hL1 := length_ge_one hL
  have hLp := length_pos hL
  have hCs := Cs_pos
  have hfac : (2 : ℝ)^135 ≤ Cs^3*L^9 :=
    ((by norm_num : (2 : ℝ)^135 ≤ 2^512).trans H1_constant_le_Cs).trans
      ((le_self_pow₀ Cs_ge_one (by decide : (3 : ℕ) ≠ 0)).trans
        (le_mul_of_one_le_right (pow_nonneg Cs_pos.le 3) (one_le_pow₀ hL1)))
  have hp := mul_le_mul_of_nonneg_right hfac (show 0 ≤ Cs*L^3*ζ by positivity)
  have he : Cs^3*L^9*(Cs*L^3*ζ)=Cs^4*L^12*ζ := by ring
  rw [he] at hp
  apply le_trans _ (hp.trans htest)
  apply le_of_eq
  field_simp
  ring

#print axioms source_forcing_budget

end Maxwell.Continuum.Parameters
