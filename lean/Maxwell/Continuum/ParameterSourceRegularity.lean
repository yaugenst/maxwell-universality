import Maxwell.Continuum.ParameterAssembly

/-! Numerical absorption of the actual finite-source translation and field
regularity estimates into the manuscript's master budgets. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem source_translation_numeric {L K α B F fa V G : ℝ}
    (hL : 1 ≤ L) (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hG : 0 ≤ G) (hF0 : 0 ≤ F) (hfa0 : 0 ≤ fa) (hV0 : 0 ≤ V)
    (hB : B ≤ 1+1024*K*L^2/α) (hF : F ≤ (2 : ℝ)^700*G)
    (hfa : fa ≤ (2 : ℝ)^140*K*G) (hV : V ≤ (2 : ℝ)^130*L⁻¹^2) :
    fa+3*(B*(F+(800*V*L⁻¹*(4*L^2)+V*448*L^4)*fa)) ≤
      (2 : ℝ)^714*K^2*α⁻¹*L^4*G := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  have hbase : 1 ≤ K*α⁻¹*L^2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hi) (one_le_pow₀ hL)
  have hB' : B ≤ (2 : ℝ)^11*K*α⁻¹*L^2 := by
    have he : 1024*K*L^2/α = 1024*(K*α⁻¹*L^2) := by ring
    rw [he] at hB
    norm_num only [show (2 : ℝ)^11 = 2048 by norm_num]
    nlinarith only [hB,hbase]
  have hfactor : 800*V*L⁻¹*(4*L^2)+V*448*L^4 ≤ (2 : ℝ)^142*L^2 := by
    have hraw := mul_le_mul_of_nonneg_right hV
      (show 0 ≤ 3200*L+448*L^4 by positivity)
    have hident : V*(3200*L+448*L^4) = 800*V*L⁻¹*(4*L^2)+V*448*L^4 := by
      field_simp
      ring
    have hid2 : (2 : ℝ)^130*L⁻¹^2*(3200*L+448*L^4) =
        (2 : ℝ)^130*(3200*L⁻¹+448*L^2) := by field_simp
    rw [hident,hid2] at hraw
    have hiL : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
    have hc : (2 : ℝ)^130*(3200*L⁻¹+448*L^2) ≤ (2 : ℝ)^142*L^2 := by
      nlinarith only [hiL,hL2]
    exact hraw.trans hc
  have hin : F+(800*V*L⁻¹*(4*L^2)+V*448*L^4)*fa ≤ (2 : ℝ)^701*K*L^2*G := by
    have hm := mul_le_mul hfactor hfa hfa0 (by positivity : 0 ≤ (2 : ℝ)^142*L^2)
    have hKG : G ≤ K*L^2*G := le_mul_of_one_le_left hG
      (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hL))
    have hf' := hF.trans (mul_le_mul_of_nonneg_left hKG (by positivity))
    have he : (2 : ℝ)^142*L^2*((2 : ℝ)^140*K*G) = (2 : ℝ)^282*K*L^2*G := by norm_num; ring
    rw [he] at hm
    have hnon : 0 ≤ K*L^2*G := by positivity
    have hc : (2 : ℝ)^700+(2 : ℝ)^282 ≤ (2 : ℝ)^701 := by norm_num
    have hp := mul_le_mul_of_nonneg_right hc hnon
    nlinarith only [hm,hf',hp]
  have hM := mul_le_mul hB' hin
    (show 0 ≤ F+(800*V*L⁻¹*(4*L^2)+V*448*L^4)*fa by positivity)
    (show 0 ≤ (2 : ℝ)^11*K*α⁻¹*L^2 by positivity)
  have heM : ((2 : ℝ)^11*K*α⁻¹*L^2)*((2 : ℝ)^701*K*L^2*G) =
      (2 : ℝ)^712*(K^2*α⁻¹*L^4*G) := by norm_num; ring
  rw [heM] at hM
  have hKG : K*G ≤ K^2*α⁻¹*L^4*G := by
    have h4 : 1 ≤ K*α⁻¹*L^4 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hi) (one_le_pow₀ hL)
    have hh := le_mul_of_one_le_right (show 0 ≤ K*G by positivity) h4
    convert hh using 1
    ring
  have hfa' : fa ≤ (2 : ℝ)^140*(K^2*α⁻¹*L^4*G) := by
    calc
      fa ≤ (2 : ℝ)^140*K*G := hfa
      _ = (2 : ℝ)^140*(K*G) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKG (by positivity)
  have hc : (2 : ℝ)^140+3*(2 : ℝ)^712 ≤ (2 : ℝ)^714 := by norm_num
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ K^2*α⁻¹*L^4*G by positivity)
  nlinarith only [hM,hfa',hp]

theorem source_H1_budget {L K α B F fa V G : ℝ}
    (hL : Ls ≤ L) (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hG : 0 ≤ G) (hF0 : 0 ≤ F) (hfa0 : 0 ≤ fa) (hV0 : 0 ≤ V)
    (hB : B ≤ 1+1024*K*L^2/α) (hF : F ≤ (2 : ℝ)^700*G)
    (hfa : fa ≤ (2 : ℝ)^140*K*G) (hV : V ≤ (2 : ℝ)^130*L⁻¹^2) :
    fa+3*(B*(F+(800*V*L⁻¹*(4*L^2)+V*448*L^4)*fa)) ≤
      Cs^4*K^2*α⁻¹*L^4*G := by
  have h := source_translation_numeric (length_ge_one hL) hK hα hα1 hG hF0 hfa0 hV0
    hB hF hfa hV
  have hc : (2 : ℝ)^714 ≤ Cs^4 :=
    (fixed_power_le_Cs (by have := exponent_large; omega)).trans
      (le_self_pow₀ Cs_ge_one (by decide : (4 : ℕ) ≠ 0))
  apply h.trans
  gcongr

theorem source_field_H1_budget {L K α F1 fa G : ℝ}
    (hL : Ls ≤ L) (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) (hG : 0 ≤ G)
    (hF1 : F1 ≤ Cs^4*K^2*α⁻¹*L^4*G) (hfa : fa ≤ (2 : ℝ)^140*K*G) :
    (4*L^2)*F1+2000*L^4*fa ≤ Cs^5*K^2*α⁻¹*L^6*G := by
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
  have h1 := mul_le_mul_of_nonneg_left hF1 (show 0 ≤ 4*L^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hfa' (show 0 ≤ 2000*L^4 by positivity)
  have hc : 4*Cs^4+2000*(2 : ℝ)^140 ≤ Cs^5 := by
    have hC : (2 : ℝ)^512 ≤ Cs := H1_constant_le_Cs
    have hC4 : Cs ≤ Cs^4 := le_self_pow₀ Cs_ge_one (by decide : (4 : ℕ) ≠ 0)
    have hsmall : 2000*(2 : ℝ)^140 ≤ Cs^4 :=
      (by norm_num : 2000*(2 : ℝ)^140 ≤ (2 : ℝ)^512).trans (hC.trans hC4)
    have h5 : (5 : ℝ) ≤ Cs := (by norm_num : (5 : ℝ) ≤ 2^512).trans hC
    have hp := mul_le_mul_of_nonneg_right h5 (pow_nonneg Cs_pos.le 4)
    nlinarith only [hsmall,hp]
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ K^2*α⁻¹*L^6*G by positivity)
  nlinarith only [h1,h2,hp]

#print axioms source_H1_budget
#print axioms source_field_H1_budget

end Maxwell.Continuum.Parameters
