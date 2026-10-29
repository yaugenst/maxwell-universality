import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

namespace Maxwell.Spectral.BoxProjection

noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def inverseVector (v : H) : H := (1 / ‖v‖)^2 • v

def projection (v : H) : H →L[ℂ] H :=
  (innerSL ℂ v).smulRight (inverseVector v)

def transverseLinearTerm (v w₁ : H) : H →L[ℂ] H :=
  (innerSL ℂ w₁).smulRight (inverseVector v)

@[simp] theorem projection_apply (v f : H) : projection v f = inner ℂ v f • inverseVector v := rfl

@[simp] theorem transverseLinearTerm_apply (v w₁ f : H) :
    transverseLinearTerm v w₁ f = inner ℂ w₁ f • inverseVector v := rfl

theorem inverseVector_norm (v : H) (hv : v ≠ 0) : ‖inverseVector v‖ = 1 / ‖v‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [inverseVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  field_simp

/-- Euclidean inversion gives the exact perturbation norm of the projector
prefactor, stronger than the estimate used by the scalar verifier. -/
theorem inverseVector_difference (v g : H) (hv : v ≠ 0) (hg : g ≠ 0) :
    ‖inverseVector g - inverseVector v‖ = ‖g - v‖ / (‖g‖ * ‖v‖) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have h := dist_div_norm_sq_smul hg hv 1
  have he : ‖inverseVector g - inverseVector v‖ =
      (1 / (‖g‖ * ‖v‖)) * ‖g-v‖ := by
    simpa only [inverseVector, dist_eq_norm, one_pow] using h
  rw [he]
  ring

omit [InnerProductSpace ℂ H] in
theorem norm_add_lower (v w : H) (s : ℝ) (hw : ‖w‖ ≤ s) :
    ‖v‖ - s ≤ ‖v + w‖ := by
  have h := norm_sub_norm_le v (-w)
  rw [norm_neg, sub_neg_eq_add] at h
  linarith

theorem inverseVector_difference_bound (v w : H) (s : ℝ)
    (hs : 0 ≤ s) (hw : ‖w‖ ≤ s) (hsmall : s < ‖v‖) :
    ‖inverseVector (v+w) - inverseVector v‖ ≤ s / (‖v‖ * (‖v‖ - s)) := by
  have hv : v ≠ 0 := norm_pos_iff.mp (hs.trans_lt hsmall)
  have hlo := norm_add_lower v w s hw
  have hg : v + w ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr hsmall).trans_le hlo)
  rw [inverseVector_difference v (v+w) hv hg, add_sub_cancel_left]
  apply div_le_div₀ hs hw (by positivity)
  nlinarith [norm_nonneg v]

theorem projection_transverse (v w f : H) (hf : inner ℂ v f = 0) :
    projection (v+w) f = inner ℂ w f • inverseVector (v+w) := by
  simp only [projection_apply, inner_add_left, hf, zero_add]

theorem projection_eq_starProjection (v : H) : projection v = (ℂ ∙ v).starProjection := by
  ext f
  rw [projection_apply, Submodule.starProjection_singleton]
  simp only [inverseVector, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hc : (((1/‖v‖)^2 : ℝ) : ℂ) = (((‖v‖^2 : ℝ) : ℂ))⁻¹ := by
    push_cast
    ring
  change (inner ℂ v f * (((1/‖v‖)^2 : ℝ) : ℂ)) • v = _
  rw [hc, div_eq_mul_inv]
  rfl

theorem projection_transverse_bound (v w f : H) (s : ℝ)
    (hs : 0 ≤ s) (hw : ‖w‖ ≤ s) (hsmall : s < ‖v‖) (hf : inner ℂ v f = 0) :
    ‖projection (v+w) f‖ ≤ s / (‖v‖-s) * ‖f‖ := by
  have hlo := norm_add_lower v w s hw
  have hg : v+w ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr hsmall).trans_le hlo)
  rw [projection_transverse v w f hf, norm_smul, inverseVector_norm _ hg]
  calc
    _ ≤ (s*‖f‖) * (1/(‖v‖-s)) := by
      apply mul_le_mul
      · exact (norm_inner_le_norm w f).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg f))
      · exact one_div_le_one_div_of_le (sub_pos.mpr hsmall) hlo
      · positivity
      · positivity
    _ = _ := by ring

/-- The loss of the old gradient direction under the new transverse
projection is controlled by the symbol increment itself. -/
theorem gradient_transverse_bound (v w : H) :
    ‖v - projection (v+w) v‖ ≤ ‖w‖ := by
  rw [projection_eq_starProjection, Submodule.starProjection_minimal]
  apply (ciInf_le (show BddBelow (Set.range (fun x : (ℂ ∙ (v+w)) => ‖v-(x:H)‖)) from
    ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩)
    (⟨v+w, Submodule.mem_span_singleton_self _⟩ : ℂ ∙ (v+w))).trans
  simp

theorem projection_pythagorean (v u : H) :
    ‖u‖^2 = ‖projection v u‖^2 + ‖u-projection v u‖^2 := by
  rw [projection_eq_starProjection]
  simpa only [Submodule.starProjection_orthogonal_val] using
    Submodule.norm_sq_eq_add_norm_sq_starProjection u (ℂ ∙ v)

theorem gradient_projection_lower (v w : H) :
    ‖v‖^2-‖w‖^2 ≤ ‖projection (v+w) v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (gradient_transverse_bound v w) 2
  have heq := projection_pythagorean (v+w) v
  linarith

theorem projection_inner (v f g : H) :
    inner ℂ (projection v f) g = inner ℂ f (projection v g) := by
  rw [projection_eq_starProjection]
  exact Submodule.inner_starProjection_left_eq_right (ℂ ∙ v) f g

theorem inverseVector_inner_self (v : H) (hv : v ≠ 0) :
    inner ℂ (inverseVector v) v = 1 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [inverseVector, inner_smul_left_eq_smul, inner_self_eq_norm_sq_to_K]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  change (((1/‖v‖)^2 : ℝ) : ℂ) * (‖v‖ : ℂ)^2 = 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  norm_cast
  field_simp

theorem transverseLinearTerm_inner_center (v w f : H) (hv : v ≠ 0) :
    inner ℂ (transverseLinearTerm v w f) v = inner ℂ f w := by
  rw [transverseLinearTerm_apply, inner_smul_left, inverseVector_inner_self v hv, mul_one]
  exact inner_conj_symm (𝕜 := ℂ) f w

theorem mixed_remainder_identity (v w w₁ f : H) (hv : v ≠ 0) :
    inner ℂ f (projection (v+w) v-w₁) =
      inner ℂ (projection (v+w) f-transverseLinearTerm v w₁ f) v := by
  rw [inner_sub_right, inner_sub_left, projection_inner,
    transverseLinearTerm_inner_center v w₁ f hv]

theorem transverse_remainder_identity (v w w₁ f : H) (hf : inner ℂ v f = 0) :
    projection (v+w) f - transverseLinearTerm v w₁ f =
      inner ℂ w f • (inverseVector (v+w) - inverseVector v) +
        inner ℂ (w-w₁) f • inverseVector v := by
  rw [projection_transverse v w f hf, transverseLinearTerm_apply, inner_sub_left]
  module

/-- The center-transverse projector remainder is genuinely quadratic in
the symbol displacement and its first-order remainder. -/
theorem transverse_remainder_bound_sharp (v w w₁ f : H) (s : ℝ)
    (hs : 0 ≤ s) (hw : ‖w‖ ≤ s) (hsmall : s < ‖v‖)
    (hrem : ‖w-w₁‖ ≤ s^2/2) (hf : inner ℂ v f = 0) :
    ‖projection (v+w) f - transverseLinearTerm v w₁ f‖ ≤
      s^2 * (1/(‖v‖*(‖v‖-s)) + 1/(2*‖v‖)) * ‖f‖ := by
  have hv : v ≠ 0 := norm_pos_iff.mp (hs.trans_lt hsmall)
  rw [transverse_remainder_identity v w w₁ f hf]
  calc
    _ ≤ ‖inner ℂ w f • (inverseVector (v+w) - inverseVector v)‖ +
        ‖inner ℂ (w-w₁) f • inverseVector v‖ := norm_add_le _ _
    _ = ‖inner ℂ w f‖ * ‖inverseVector (v+w) - inverseVector v‖ +
        ‖inner ℂ (w-w₁) f‖ * ‖inverseVector v‖ := by rw [norm_smul, norm_smul]
    _ ≤ (s*‖f‖) * (s/(‖v‖*(‖v‖-s))) + (s^2/2*‖f‖) * (1/‖v‖) := by
      gcongr
      · exact (norm_inner_le_norm w f).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg f))
      · exact inverseVector_difference_bound v w s hs hw hsmall
      · exact (norm_inner_le_norm (w-w₁) f).trans
          (mul_le_mul_of_nonneg_right hrem (norm_nonneg f))
      · exact (inverseVector_norm v hv).le
    _ = _ := by ring

/-- This is exactly the projector remainder coefficient PR used by the
Bloch-box acceptance program. -/
theorem transverse_remainder_bound (v w w₁ f : H) (s : ℝ)
    (hs : 0 ≤ s) (hw : ‖w‖ ≤ s) (hsmall : s < ‖v‖)
    (hrem : ‖w-w₁‖ ≤ s^2/2) (hf : inner ℂ v f = 0) :
    ‖projection (v+w) f - transverseLinearTerm v w₁ f‖ ≤
      s^2 * (1/(2*‖v‖) + (3+s/‖v‖)/(‖v‖-s)^2) * ‖f‖ := by
  apply (transverse_remainder_bound_sharp v w w₁ f s hs hw hsmall hrem hf).trans
  have hr : 0 < ‖v‖ := hs.trans_lt hsmall
  have hd : 0 < ‖v‖ - s := sub_pos.mpr hsmall
  have hc : 1/(‖v‖*(‖v‖-s)) ≤ (3+s/‖v‖)/(‖v‖-s)^2 := by
    apply (div_le_div_iff₀ (mul_pos hr hd) (sq_pos_of_pos hd)).mpr
    field_simp
    nlinarith
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg s)
  linarith only [hc]

theorem mixed_remainder_bound_sharp (v w w₁ f : H) (s : ℝ)
    (hs : 0 ≤ s) (hw : ‖w‖ ≤ s) (hsmall : s < ‖v‖)
    (hrem : ‖w-w₁‖ ≤ s^2/2) (hf : inner ℂ v f = 0) :
    ‖inner ℂ f (projection (v+w) v-w₁)‖ ≤
      s^2*(1/(‖v‖*(‖v‖-s))+1/(2*‖v‖))*‖f‖*‖v‖ := by
  rw [mixed_remainder_identity v w w₁ f (norm_pos_iff.mp (hs.trans_lt hsmall))]
  apply (norm_inner_le_norm _ _).trans
  exact mul_le_mul_of_nonneg_right
    (transverse_remainder_bound_sharp v w w₁ f s hs hw hsmall hrem hf) (norm_nonneg _)

end
end Maxwell.Spectral.BoxProjection
