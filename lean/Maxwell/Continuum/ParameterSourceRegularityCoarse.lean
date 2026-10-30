import Maxwell.Continuum.ParameterSourceRegularity

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem source_field_H1_budget_coarse {L K α F1 fa G : ℝ}
    (hL : Ls ≤ L) (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) (hG : 0 ≤ G)
    (hF1 : F1 ≤ Cs^4*K^2*α⁻¹*L^4*G) (hfa : fa ≤ (2 : ℝ)^140*K*G) :
    (16*L^2)*F1+2000*L^4*fa ≤ Cs^5*K^2*α⁻¹*L^6*G := by
  have hLp := length_pos hL
  have hL1 := length_ge_one hL
  have hKp := zero_lt_one.trans_le hK
  have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  have hKG : K*G ≤ K^2*α⁻¹*L^2*G := by
    have h4 : 1 ≤ K*α⁻¹*L^2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hi) (one_le_pow₀ hL1)
    have hh := le_mul_of_one_le_right (show 0 ≤ K*G by positivity) h4
    convert hh using 1
    ring
  have hfa' : fa ≤ (2 : ℝ)^140*(K^2*α⁻¹*L^2*G) := by
    calc
      fa ≤ (2 : ℝ)^140*K*G := hfa
      _ = (2 : ℝ)^140*(K*G) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKG (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hF1 (show 0 ≤ 16*L^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hfa' (show 0 ≤ 2000*L^4 by positivity)
  have hc : 16*Cs^4+2000*(2 : ℝ)^140 ≤ Cs^5 := by
    have hC : (2 : ℝ)^512 ≤ Cs := H1_constant_le_Cs
    have hC4 : Cs ≤ Cs^4 := le_self_pow₀ Cs_ge_one (by decide : (4 : ℕ) ≠ 0)
    have hsmall : 2000*(2 : ℝ)^140 ≤ Cs^4 :=
      (by norm_num : 2000*(2 : ℝ)^140 ≤ (2 : ℝ)^512).trans (hC.trans hC4)
    have h5 : (17 : ℝ) ≤ Cs := (by norm_num : (17 : ℝ) ≤ 2^512).trans hC
    have hp := mul_le_mul_of_nonneg_right h5 (pow_nonneg Cs_pos.le 4)
    nlinarith only [hsmall,hp]
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ K^2*α⁻¹*L^6*G by positivity)
  nlinarith only [h1,h2,hp]

#print axioms source_field_H1_budget_coarse

end Maxwell.Continuum.Parameters
