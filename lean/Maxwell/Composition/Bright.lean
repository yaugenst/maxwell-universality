import Maxwell.Composition.SourceIdentity
import Maxwell.Composition.Woodbury
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual bright Schur perturbations and their constructed inverses. -/

namespace Maxwell.Composition

section SchurError

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The mixed-block correction is quadratic. The raw bright error and
mixed block estimates are genuine operator-norm bounds on the whole union
of defects, so no number of defects enters this conclusion. -/
theorem bright_schur_error_bound
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (T : B →L[ℝ] B) (C0 Dstar ζ : ℝ)
    (hC0 : 0 ≤ C0) (hDstar : 0 ≤ Dstar) (hζ : 0 ≤ ζ)
    (hraw : ‖P.comp (M.comp U) - T‖ ≤ (256 * C0 + 5) * ζ ^ 2)
    (hE : ‖P.comp (M.comp Z)‖ ≤ (64 * C0 + 1) * ζ)
    (hC : ‖R.comp (M.comp U)‖ ≤ (64 * C0 + 1) * ζ)
    (hD : ‖(Dc.symm : C →L[ℝ] C)‖ ≤ Dstar) :
    ‖brightSchurOperator M U Z P R Dc - T‖ ≤
      (256 * C0 + 5 + Dstar * (64 * C0 + 1) ^ 2) * ζ ^ 2 := by
  have hscale : 0 ≤ (64 * C0 + 1) * ζ := by positivity
  have hinner : ‖(Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U))‖ ≤
      Dstar * ((64 * C0 + 1) * ζ) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hD hC (norm_nonneg _) hDstar)
  have hcorrection : ‖(P.comp (M.comp Z)).comp
      ((Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U)))‖ ≤
      ((64 * C0 + 1) * ζ) * (Dstar * ((64 * C0 + 1) * ζ)) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hE hinner (norm_nonneg _) hscale)
  unfold brightSchurOperator
  rw [sub_right_comm]
  calc
    _ ≤ ‖P.comp (M.comp U) - T‖ +
        ‖(P.comp (M.comp Z)).comp
          ((Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U)))‖ := norm_sub_le _ _
    _ ≤ (256 * C0 + 5) * ζ ^ 2 +
        ((64 * C0 + 1) * ζ) * (Dstar * ((64 * C0 + 1) * ζ)) :=
      add_le_add hraw hcorrection
    _ = _ := by ring

end SchurError

section BrightInverse

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem bright_perturbation_product_bound (T : B ≃L[ℝ] B) (Δ : B →L[ℝ] B)
    (α ε K : ℝ) (hα : 0 < α) (hK : 0 < K)
    (hT : ‖(T.symm : B →L[ℝ] B)‖ ≤ 16 * K / α)
    (hΔ : ‖Δ‖ ≤ α * ε / (4096 * K)) :
    ‖(T.symm : B →L[ℝ] B)‖ * ‖Δ‖ ≤ ε / 256 := by
  calc
    _ ≤ (16 * K / α) * (α * ε / (4096 * K)) :=
      mul_le_mul hT hΔ (norm_nonneg _) (by positivity)
    _ = ε / 256 := by field_simp; ring

variable [CompleteSpace B]

/-- The inverse of the actual perturbed bright block is constructed by
the convergent Neumann series, then bounded by the paper's 32 Kbar/alpha. -/
theorem bright_inverse_norm_le (T : B ≃L[ℝ] B) (Δ : B →L[ℝ] B)
    (α ε K : ℝ) (hα : 0 < α) (hK : 0 < K)
    (hεhalf : ε ≤ 1 / 2)
    (hT : ‖(T.symm : B →L[ℝ] B)‖ ≤ 16 * K / α)
    (hΔ : ‖Δ‖ ≤ α * ε / (4096 * K))
    (hsmall : ‖(T.symm : B →L[ℝ] B)‖ * ‖Δ‖ < 1) :
    ‖((perturbationEquiv T Δ hsmall).symm : B →L[ℝ] B)‖ ≤ 32 * K / α := by
  have hprod := bright_perturbation_product_bound T Δ α ε K hα hK hT hΔ
  have hden : (1 / 2 : ℝ) ≤ 1 - ‖(T.symm : B →L[ℝ] B)‖ * ‖Δ‖ := by linarith
  calc
    _ ≤ ‖(T.symm : B →L[ℝ] B)‖ /
        (1 - ‖(T.symm : B →L[ℝ] B)‖ * ‖Δ‖) :=
      perturbation_full_inverse_norm_le T Δ hsmall
    _ ≤ ‖(T.symm : B →L[ℝ] B)‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ ≤ (16 * K / α) / (1 / 2) := div_le_div_of_nonneg_right hT (by norm_num)
    _ = 32 * K / α := by ring

end BrightInverse

end Maxwell.Composition
