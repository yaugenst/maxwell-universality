import Maxwell.Continuum.FourierWeakDerivative
import Maxwell.Continuum.TranslationContinuity

/-! A local L² translation modulus yields three actual weak field
coordinate derivatives. The resulting norm is the usual inhomogeneous H¹ norm. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology

/-- A field has H¹ regularity precisely when all nine scalar coordinate
partials are represented by L² functions. -/
structure H1Data (f : FieldL2) where
  derivative : Fin 3 → FieldL2
  weak_derivative : ∀ j k, partialDistribution j (Lp.toTemperedDistribution (f k)) =
    Lp.toTemperedDistribution (derivative j k)

def H1Data.norm {f : FieldL2} (D : H1Data f) : ℝ :=
  Real.sqrt (‖f‖ ^ 2 + ∑ j : Fin 3, ‖D.derivative j‖ ^ 2)

theorem H1Data.derivative_unique {f : FieldL2} (D E : H1Data f) : D.derivative = E.derivative := by
  funext j
  apply fieldDistribution_injective
  funext k
  exact (D.weak_derivative j k).symm.trans (E.weak_derivative j k)

theorem H1Data.norm_eq {f : FieldL2} (D E : H1Data f) : D.norm = E.norm := by
  simp only [H1Data.norm, D.derivative_unique E]

theorem component_translation_bound (f : FieldL2) {M : ℝ}
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖)
    (j k : Fin 3) :
    ∀ᶠ t : ℝ in 𝓝 0, ‖translation (t • coordinateDirection j) (f k) - f k‖ ≤ M * |t| := by
  have ht : Tendsto (fun t : ℝ => t • coordinateDirection j) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t • coordinateDirection j) := by fun_prop
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  filter_upwards [ht.eventually hbound] with t hb
  have hc := PiLp.norm_apply_le (fieldTranslation (t • coordinateDirection j) f - f) k
  change ‖translation (t • coordinateDirection j) (f k) - f k‖ ≤ _ at hc
  exact hc.trans (by simpa only [coordinate_shift_norm] using hb)

def h1OfTranslation (f : FieldL2) {M : ℝ}
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖) : H1Data f where
  derivative j := WithLp.toLp 2 (fun k =>
    weakDerivative j (f k) (component_translation_bound f hbound j k))
  weak_derivative j k := weakDerivative_distribution j (f k) (component_translation_bound f hbound j k)

theorem h1OfTranslation_component_norm_le (f : FieldL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖)
    (j k : Fin 3) : ‖(h1OfTranslation f hbound).derivative j k‖ ≤ M :=
  weakDerivative_norm_le j (f k) hM (component_translation_bound f hbound j k)

theorem h1OfTranslation_direction_sq_le (f : FieldL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖)
    (j : Fin 3) : ‖(h1OfTranslation f hbound).derivative j‖ ^ 2 ≤ 3 * M ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _ : Fin 3, M ^ 2 := Finset.sum_le_sum fun k _ =>
      (sq_le_sq₀ (norm_nonneg _) hM).mpr (h1OfTranslation_component_norm_le f hM hbound j k)
    _ = 3 * M ^ 2 := by simp

theorem h1OfTranslation_gradient_sq_le (f : FieldL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖) :
    ∑ j : Fin 3, ‖(h1OfTranslation f hbound).derivative j‖ ^ 2 ≤ 9 * M ^ 2 := by
  calc
    _ ≤ ∑ _ : Fin 3, 3 * M ^ 2 := Finset.sum_le_sum fun j _ =>
      h1OfTranslation_direction_sq_le f hM hbound j
    _ = 9 * M ^ 2 := by simp; ring

theorem h1OfTranslation_norm_le (f : FieldL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a f - f‖ ≤ M * ‖a‖) :
    (h1OfTranslation f hbound).norm ≤ ‖f‖ + 3 * M := by
  rw [H1Data.norm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hg := h1OfTranslation_gradient_sq_le f hM hbound
    nlinarith [norm_nonneg f, mul_nonneg (norm_nonneg f) hM]

end Maxwell.Continuum.FourierSobolev
