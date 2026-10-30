import Maxwell.Continuum.SchwartzMultiplier
import Maxwell.Continuum.BoundaryCellH1

/-! Smooth coefficient multipliers supported in a finite union of
physical cells are controlled by the actual localized field norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory CellGauge FourierSobolev

theorem scalar_family_eq (θ : SchwartzMap Space ℂ) (F : Finset Bloch.Alias)
    (hθ : ∀ x, cellIndex x ∉ F → θ x = 0) (f : FieldL2) (j : Fin 3) :
    scalar θ (f j) = scalar θ (familyProjection F f j) := by
  apply Lp.ext
  filter_upwards [scalar_ae θ (f j), scalar_ae θ (familyProjection F f j),
    familyProjection_ae F f j] with x hl hr hF
  rw [hl, hr, hF]
  by_cases hx : cellIndex x ∈ F
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx, hθ x hx, zero_mul, zero_mul]

theorem scalar_family_norm {C : ℝ} (hC : 0 ≤ C) (θ : SchwartzMap Space ℂ)
    (hc : ∀ x, ‖θ x‖ ≤ C) (F : Finset Bloch.Alias)
    (hθ : ∀ x, cellIndex x ∉ F → θ x = 0) (f : FieldL2) (j : Fin 3) :
    ‖scalar θ (f j)‖ ≤ C*‖familyProjection F f‖ := by
  rw [scalar_family_eq θ F hθ f j]
  exact (scalar_norm_le θ hc _).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (familyProjection F f) j) hC)

theorem localH1Norm_nonneg {f : FieldL2} (Df : H1Data f) (F : Finset Bloch.Alias) :
    0 ≤ localH1Norm Df F := Real.sqrt_nonneg _

theorem localH1Norm_field {f : FieldL2} (Df : H1Data f) (F : Finset Bloch.Alias) :
    ‖familyProjection F f‖ ≤ localH1Norm Df F := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem localH1Norm_derivative {f : FieldL2} (Df : H1Data f) (F : Finset Bloch.Alias) (j : Fin 3) :
    ‖familyProjection F (Df.derivative j)‖ ≤ localH1Norm Df F := by
  apply Real.le_sqrt_of_sq_le
  apply (Finset.single_le_sum
    (fun k _ => sq_nonneg ‖familyProjection F (Df.derivative k)‖) (Finset.mem_univ j)).trans
  exact le_add_of_nonneg_left (sq_nonneg _)

#print axioms scalar_family_norm

end Maxwell.Continuum.SchwartzMultiplier
