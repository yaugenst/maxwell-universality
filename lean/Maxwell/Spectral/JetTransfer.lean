import Maxwell.Spectral.Perturbation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace Maxwell.Spectral.JetTransfer

noncomputable section

variable {H V : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Norm control for replacing both factors of a compressed Gram product. -/
theorem adjoint_product_error (A B C D : V →L[ℂ] H) :
    ‖A.adjoint.comp B - C.adjoint.comp D‖ ≤
      ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  have he : A.adjoint.comp B - C.adjoint.comp D =
      (A - C).adjoint.comp B + C.adjoint.comp (B - D) := by
    rw [map_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using
      (A - C).adjoint.opNorm_comp_le B)
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using
      C.adjoint.opNorm_comp_le (B - D)))

theorem mixed_compression_error (A : H →L[ℂ] H) (Φ U Y Z : V →L[ℂ] H) :
    ‖Φ.adjoint.comp (A.comp Y) - U.adjoint.comp (A.comp Z)‖ ≤
      ‖Φ - U‖ * ‖A‖ * ‖Y‖ + ‖U‖ * ‖A‖ * ‖Y - Z‖ := by
  have h := adjoint_product_error Φ (A.comp Y) U (A.comp Z)
  rw [← ContinuousLinearMap.comp_sub] at h
  have h1 := mul_le_mul_of_nonneg_left (A.opNorm_comp_le Y) (norm_nonneg (Φ - U))
  have h2 := mul_le_mul_of_nonneg_left (A.opNorm_comp_le (Y - Z)) (norm_nonneg U)
  calc
    _ ≤ ‖Φ - U‖ * ‖A.comp Y‖ + ‖U‖ * ‖A.comp (Y - Z)‖ := h
    _ ≤ ‖Φ - U‖ * (‖A‖ * ‖Y‖) + ‖U‖ * (‖A‖ * ‖Y - Z‖) := add_le_add h1 h2
    _ = _ := by ring

theorem compression_error (A : H →L[ℂ] H) (Φ U : V →L[ℂ] H) :
    ‖Φ.adjoint.comp (A.comp Φ) - U.adjoint.comp (A.comp U)‖ ≤
      ‖Φ - U‖ * ‖A‖ * (‖Φ‖ + ‖U‖) := by
  convert mixed_compression_error A Φ U Φ U using 1
  ring

/-- The effective quadratic coefficient is stable under the proved frame
and corrector replacements. No Hessian closeness is supplied as a premise. -/
theorem effective_quadratic_error (A₁ A₂ : H →L[ℂ] H)
    (Φ U Y Z : V →L[ℂ] H) :
    ‖(Φ.adjoint.comp (A₂.comp Φ) - Φ.adjoint.comp (A₁.comp Y)) -
        (U.adjoint.comp (A₂.comp U) - U.adjoint.comp (A₁.comp Z))‖ ≤
      ‖Φ - U‖ * ‖A₂‖ * (‖Φ‖ + ‖U‖) +
      (‖Φ - U‖ * ‖A₁‖ * ‖Y‖ + ‖U‖ * ‖A₁‖ * ‖Y - Z‖) := by
  have he : (Φ.adjoint.comp (A₂.comp Φ) - Φ.adjoint.comp (A₁.comp Y)) -
        (U.adjoint.comp (A₂.comp U) - U.adjoint.comp (A₁.comp Z)) =
      (Φ.adjoint.comp (A₂.comp Φ) - U.adjoint.comp (A₂.comp U)) -
        (Φ.adjoint.comp (A₁.comp Y) - U.adjoint.comp (A₁.comp Z)) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (compression_error A₂ Φ U)
    (mixed_compression_error A₁ Φ U Y Z))

omit [CompleteSpace H] [CompleteSpace V] in
theorem residual_error (A₁ A₂ : H →L[ℂ] H) (Φ U Y Z : V →L[ℂ] H) :
    ‖(A₂.comp Φ - A₁.comp Y) - (A₂.comp U - A₁.comp Z)‖ ≤
      ‖A₂‖ * ‖Φ - U‖ + ‖A₁‖ * ‖Y - Z‖ := by
  have he : (A₂.comp Φ - A₁.comp Y) - (A₂.comp U - A₁.comp Z) =
      A₂.comp (Φ - U) - A₁.comp (Y - Z) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (A₂.opNorm_comp_le (Φ - U))
    (A₁.opNorm_comp_le (Y - Z)))

theorem residual_gram_error (R S : V →L[ℂ] H) :
    ‖R.adjoint.comp R - S.adjoint.comp S‖ ≤ ‖R - S‖ * (‖R‖ + ‖S‖) := by
  convert adjoint_product_error R R S S using 1
  ring

omit [CompleteSpace H] [CompleteSpace V] in
/-- Transport a saved corrector residual from its rounded spectral shift
and approximate frame to the exact shift and exact frame. -/
theorem corrector_residual_transport (T A : H →L[ℂ] H)
    (Φ U Y : V →L[ℂ] H) (E z : ℝ) :
    ‖(T - (E : ℂ) • ContinuousLinearMap.id ℂ H).comp Y - A.comp Φ‖ ≤
      ‖(T - (z : ℂ) • ContinuousLinearMap.id ℂ H).comp Y - A.comp U‖ +
        |z - E| * ‖Y‖ + ‖A‖ * ‖U - Φ‖ := by
  have he : (T - (E : ℂ) • ContinuousLinearMap.id ℂ H).comp Y - A.comp Φ =
      ((T - (z : ℂ) • ContinuousLinearMap.id ℂ H).comp Y - A.comp U) +
        ((z - E : ℝ) : ℂ) • Y + A.comp (U - Φ) := by
    ext x
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, Complex.ofReal_sub, map_sub]
    module
  rw [he]
  have h := (norm_add_le
    (((T - (z : ℂ) • ContinuousLinearMap.id ℂ H).comp Y - A.comp U) +
      ((z - E : ℝ) : ℂ) • Y) (A.comp (U - Φ))).trans
    (add_le_add (norm_add_le _ _) (A.opNorm_comp_le (U - Φ)))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using h

omit [CompleteSpace H] [CompleteSpace V] in
/-- Transport a certified quadratic lower bound by a proved operator error. -/
theorem quadratic_lower_transfer (K L : V →L[ℂ] V) (a ε : ℝ)
    (herror : ‖K - L‖ ≤ ε)
    (hL : ∀ x, a * ‖x‖ ^ 2 ≤ Complex.re (inner ℂ x (L x))) (x : V) :
    (a - ε) * ‖x‖ ^ 2 ≤ Complex.re (inner ℂ x (K x)) := by
  have h := quadratic_le_add_of_norm_sub_le L K ε
    (by simpa only [norm_sub_rev] using herror) x
  have hl := hL x
  nlinarith only [h, hl]

omit [CompleteSpace H] [CompleteSpace V] in
theorem quadratic_upper_transfer (K L : V →L[ℂ] V) (a ε : ℝ)
    (herror : ‖K - L‖ ≤ ε)
    (hL : ∀ x, Complex.re (inner ℂ x (L x)) ≤ a * ‖x‖ ^ 2) (x : V) :
    Complex.re (inner ℂ x (K x)) ≤ (a + ε) * ‖x‖ ^ 2 := by
  have h := quadratic_le_add_of_norm_sub_le K L ε herror x
  have hl := hL x
  nlinarith only [h, hl]

end
end Maxwell.Spectral.JetTransfer
