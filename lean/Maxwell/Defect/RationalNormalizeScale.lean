import Maxwell.Defect.RationalNormalize
import Maxwell.Defect.ModePowerInteger

/-! Integer normalization does not need to divide every mode coordinate
by its common denominator. Scaling the norm upper bound by the same factor
leaves the computed rational normalized output exactly unchanged. -/
namespace Maxwell.Defect
open Cost.CalibrationMatrix FiniteStencil
variable {n : ℕ}

theorem rationalNormSq_smul (c : ℚ) (v : Fin n → ℚ) :
    rationalNormSq (c • v) = c ^ 2 * rationalNormSq v := by
  simp only [rationalNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

namespace RationalNormalize

theorem denominator_smul (c : ℚ) (hc : c ≠ 0) (v : Fin n → ℚ) (B : ℚ) (p : ℕ) :
    denominator (c • v) (c * B) p = c * denominator v B p := by
  have hr : rationalNormSq (c • v) / (c * B)^2 = rationalNormSq v / B^2 := by
    rw [rationalNormSq_smul, mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)
  simp only [denominator, hr]
  ring

theorem vector_smul (c : ℚ) (hc : c ≠ 0) (v : Fin n → ℚ) (B : ℚ) (p : ℕ) :
    vector (c • v) (c * B) p = vector v B p := by
  rw [vector, denominator_smul c hc, smul_smul, mul_inv_rev]
  have he : ((denominator v B p)⁻¹ * c⁻¹) * c = (denominator v B p)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [he]
  rfl

/-- Exact binding from the two-channel integer mode vector to the existing
rational normalization routine. Only the scalar upper bound is rescaled. -/
theorem integerPower_vector_eq (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (D V : ℕ) (hD : 0 < D) (hV : 0 < V)
    (hT : ∀ i j, (T i j).den ∣ D) (hv : ∀ i, (v i).den ∣ V)
    (N : ℕ) (B : ℚ) (p : ℕ) :
    vector (fun i => ((channelPower (integerMatrix T D) (integerSource v V) N).value i : ℚ))
      (((V : ℚ) * (D : ℚ)^N) * B) p = vector (rationalPowerAction T N v) B p := by
  have hscale : (fun i => ((channelPower (integerMatrix T D) (integerSource v V) N).value i : ℚ)) =
      ((V : ℚ) * (D : ℚ)^N) • rationalPowerAction T N v := by
    funext i
    exact channelPower_scaled _ _ T v D V (integerMatrix_scaled T D hT)
      (integerSource_scaled v V hv) N i
  rw [hscale]
  exact vector_smul _ (by positivity) _ _ _

end RationalNormalize
end Maxwell.Defect
