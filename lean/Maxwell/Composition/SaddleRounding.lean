import Maxwell.Composition.RectangularMatrix
import Maxwell.Perturbation

/-! The original real saddle residual survives coefficient and source
rounding with the manuscript's explicit margin. -/
noncomputable section
namespace Maxwell.Composition.RectangularSaddle
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]
set_option maxHeartbeats 800000

theorem rounded_operator_bounds (A : E ≃L[ℝ] E) (Ahat : E →L[ℝ] E)
    (Q η : ℝ) (hQ : 1 ≤ Q) (hη : η ≤ 1)
    (hA : ‖(A : E →L[ℝ] E)‖ ≤ 2)
    (hinv : ‖(A.symm : E →L[ℝ] E)‖ ≤ Q)
    (herr : ‖Ahat - (A : E →L[ℝ] E)‖ ≤ η/(512*Q)) :
    ∃ U : (E →L[ℝ] E)ˣ, (U : E →L[ℝ] E) = Ahat ∧
      ‖(↑U⁻¹ : E →L[ℝ] E)‖ ≤ 2*Q ∧ ‖Ahat‖ ≤ 3 := by
  have hQ0 : 0 < Q := by linarith
  have herr0 : 0 ≤ η/(512*Q) := (norm_nonneg _).trans herr
  have hsmall : ‖(A.symm : E →L[ℝ] E)‖ * ‖Ahat - (A : E →L[ℝ] E)‖ ≤ 1/2 := by
    calc
      _ ≤ Q*(η/(512*Q)) := mul_le_mul hinv herr (norm_nonneg _) hQ0.le
      _ = η/512 := by field_simp
      _ ≤ 1/2 := by linarith
  obtain ⟨U, hU, hUi⟩ := unit_perturbation_inverse_bound A.toUnit
    (Ahat - (A : E →L[ℝ] E)) hsmall
  have hU' : (U : E →L[ℝ] E) = Ahat := by
    change (U : E →L[ℝ] E) = (A : E →L[ℝ] E) + (Ahat - (A : E →L[ℝ] E)) at hU
    convert hU using 1
    abel
  refine ⟨U, hU', hUi.trans (mul_le_mul_of_nonneg_left hinv (by norm_num)), ?_⟩
  have heq : Ahat = (A : E →L[ℝ] E) + (Ahat - (A : E →L[ℝ] E)) := by abel
  rw [heq]
  apply (norm_add_le _ _).trans
  have he : η/(512*Q) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith

omit [CompleteSpace E] [Nontrivial E] in
theorem unrounded_residual_bound (A Ahat : E →L[ℝ] E)
    (U : (E →L[ℝ] E)ˣ) (hU : (U : E →L[ℝ] E) = Ahat)
    (Q η : ℝ) (hQ : 1 ≤ Q) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hinv : ‖(↑U⁻¹ : E →L[ℝ] E)‖ ≤ 2*Q)
    (herr : ‖Ahat-A‖ ≤ η/(512*Q)) (b bhat x : E)
    (hsource : ‖bhat-b‖ ≤ (η/1024)*‖b‖)
    (hres : ‖Ahat x-bhat‖ ≤ (η/64)*‖bhat‖) :
    ‖x‖ ≤ 3*Q*‖b‖ ∧ ‖A x-b‖ ≤ (η/16)*‖b‖ := by
  have hQ0 : 0 < Q := by linarith
  have hb : ‖bhat‖ ≤ (1025/1024 : ℝ)*‖b‖ := by
    have hh := norm_add_le (bhat-b) b
    rw [sub_add_cancel] at hh
    have hηb := mul_le_mul_of_nonneg_right hη (norm_nonneg b)
    nlinarith
  have hx : ‖x‖ ≤ 3*Q*‖b‖ := by
    have hinverse : (↑U⁻¹ : E →L[ℝ] E) (Ahat x) = x := by
      rw [← hU]
      exact congrArg (fun T : E →L[ℝ] E => T x) U.inv_mul
    have hnx := (↑U⁻¹ : E →L[ℝ] E).le_opNorm (Ahat x)
    rw [hinverse] at hnx
    have har : ‖Ahat x‖ ≤ (65/64 : ℝ)*‖bhat‖ := by
      have hh := norm_add_le (Ahat x-bhat) bhat
      rw [sub_add_cancel] at hh
      have hηb := mul_le_mul_of_nonneg_right hη (norm_nonneg bhat)
      nlinarith
    calc
      ‖x‖ ≤ (2*Q)*‖Ahat x‖ := hnx.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
      _ ≤ (2*Q)*((65/64)*((1025/1024)*‖b‖)) :=
        mul_le_mul_of_nonneg_left
          (har.trans (mul_le_mul_of_nonneg_left hb (by norm_num))) (by positivity)
      _ ≤ 3*Q*‖b‖ := by nlinarith [mul_nonneg hQ0.le (norm_nonneg b)]
  refine ⟨hx, ?_⟩
  have hmat : ‖A-Ahat‖*‖x‖ ≤ (3/512 : ℝ)*η*‖b‖ := by
    rw [norm_sub_rev]
    calc
      _ ≤ (η/(512*Q))*(3*Q*‖b‖) :=
        mul_le_mul herr hx (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hread : ‖Ahat x-bhat‖ ≤ (1025/65536 : ℝ)*η*‖b‖ := by
    apply hres.trans
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ η/64)
    convert hh using 1
    ring
  have hh := residual_perturbation_bound A Ahat x b bhat
  have hprod := mul_nonneg hη0 (norm_nonneg b)
  nlinarith

end Maxwell.Composition.RectangularSaddle
