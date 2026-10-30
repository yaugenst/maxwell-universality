import Maxwell.Continuum.ParameterTuning

/-! The actual rounded eigenvalue and target diagonal leave a positive
denominator before the finite scalar reciprocal is rounded. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs Ls exponent
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

theorem reciprocal_denominator_enclosure {L μ μhat θ ζ : ℝ} (hL : Ls ≤ L)
    (hμlo : (1/(2 : ℝ)^128)*L^2 ≤ μ) (hμhi : μ ≤ (1/(2 : ℝ)^90)*L^2)
    (hθ : |θ| ≤ (1/(2 : ℝ)^196)*L^2) (hμhat : |μhat-μ| ≤ ζ^2/16)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    (1/(2 : ℝ)^129)*L^2 ≤ μhat+θ ∧ μhat+θ ≤ L^2 := by
  have hl : (2 : ℝ)^100 ≤ L :=
    (power_le_Ls (by have := exponent_large; omega)).trans hL
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2^100) hl 2
  have hround : ζ^2/16 ≤ (1/(2 : ℝ)^200)*L^2 := by
    have hz : ζ^2 ≤ 1 := pow_le_one₀ hζ0 hζ1
    have hm := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1/2^200)
    have he : (1/(2 : ℝ)^200)*((2 : ℝ)^100)^2 = 1 := by norm_num
    rw [he] at hm
    exact (div_le_self (sq_nonneg ζ) (by norm_num)).trans (hz.trans hm)
  obtain ⟨hθlo, hθhi⟩ := abs_le.mp hθ
  obtain ⟨hhatlo, hhathi⟩ := abs_le.mp hμhat
  have hlo : (1/(2 : ℝ)^129) ≤ 1/2^128-1/2^196-1/2^200 := by norm_num
  have hhi : (1/(2 : ℝ)^90)+1/2^196+1/2^200 ≤ 1 := by norm_num
  have hlo' := mul_le_mul_of_nonneg_right hlo (sq_nonneg L)
  have hhi' := mul_le_mul_of_nonneg_right hhi (sq_nonneg L)
  constructor <;> nlinarith

theorem reciprocal_enclosure {L μ μhat θ ζ : ℝ} (hL : Ls ≤ L)
    (hμlo : (1/(2 : ℝ)^128)*L^2 ≤ μ) (hμhi : μ ≤ (1/(2 : ℝ)^90)*L^2)
    (hθ : |θ| ≤ (1/(2 : ℝ)^196)*L^2) (hμhat : |μhat-μ| ≤ ζ^2/16)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    L⁻¹^2 ≤ (μhat+θ)⁻¹ ∧ (μhat+θ)⁻¹ ≤ (2 : ℝ)^129*L⁻¹^2 := by
  have he := reciprocal_denominator_enclosure hL hμlo hμhi hθ hμhat hζ0 hζ1
  have hL0 := length_pos hL
  have hden : 0 < μhat+θ := (by positivity : (0 : ℝ) < (1/2^129)*L^2).trans_le he.1
  constructor
  · simpa only [← inv_pow] using (inv_le_inv₀ (pow_pos hL0 2) hden).mpr he.2
  · have hh := (inv_le_inv₀ hden (by positivity : (0 : ℝ) < (1/2^129)*L^2)).mpr he.1
    simpa only [mul_inv_rev, inv_div, inv_one, div_one, ← inv_pow, mul_comm] using hh

#print axioms reciprocal_denominator_enclosure
#print axioms reciprocal_enclosure

end Maxwell.Continuum.Parameters
