import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Full-block exponential bounds and the ellipsoid support calculation.

The Fourier phase is evaluated on the shifted contour. A bounded measurable
block density gives its integral bound, for arbitrary complex normed block
spaces. The admissible maximizing shift is constructed explicitly.
-/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

/-- A Fourier phase after a shift with real decay pairing `b`. -/
def shiftedFourierFactor (θ b : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((θ : ℂ) + Complex.I * (b : ℂ)))

theorem norm_shiftedFourierFactor (θ b : ℝ) :
    ‖shiftedFourierFactor θ b‖ = Real.exp (-b) := by
  rw [shiftedFourierFactor, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

section FourierBound

variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {μ : Measure α}

omit [NormedSpace ℝ V] in
/-- Uniform block bounds retain the exact exponential factor on a shifted
Fourier contour. -/
theorem shiftedFourierDensity_bound (θ : α → ℝ) (b C : ℝ) (R : α → V)
    (hR : ∀ᵐ q ∂μ, ‖R q‖ ≤ C) :
    ∀ᵐ q ∂μ, ‖shiftedFourierFactor (θ q) b • R q‖ ≤ C * Real.exp (-b) := by
  filter_upwards [hR] with q hq
  rw [norm_smul, norm_shiftedFourierFactor]
  exact (mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le).trans_eq (mul_comm _ _)

omit [NormedSpace ℝ V] in
/-- The shifted density is genuinely integrable on every finite measure
domain. This covers scalar entries and entire finite matrix blocks. -/
theorem shiftedFourierDensity_integrable [IsFiniteMeasure μ]
    (θ : α → ℝ) (b C : ℝ) (R : α → V)
    (hθ : Measurable θ) (hRmeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ q ∂μ, ‖R q‖ ≤ C) :
    Integrable (fun q => shiftedFourierFactor (θ q) b • R q) μ := by
  apply (integrable_const (C * Real.exp (-b))).mono' _
    (shiftedFourierDensity_bound θ b C R hR)
  apply AEStronglyMeasurable.smul _ hRmeas
  apply Measurable.aestronglyMeasurable
  unfold shiftedFourierFactor
  fun_prop

/-- The complete block integral inherits the shifted exponential decay. -/
theorem norm_integral_shiftedFourier_le [IsFiniteMeasure μ]
    (θ : α → ℝ) (b C : ℝ) (R : α → V)
    (hR : ∀ᵐ q ∂μ, ‖R q‖ ≤ C) :
    ‖∫ q, shiftedFourierFactor (θ q) b • R q ∂μ‖ ≤
      μ.real univ * C * Real.exp (-b) := by
  exact (norm_integral_le_of_norm_le_const
    (shiftedFourierDensity_bound θ b C R hR)).trans_eq (by ring)

/-- Version on a measurable integration set of finite measure, with the
domain measure displayed rather than the restricted-measure notation. -/
theorem norm_setIntegral_shiftedFourier_le
    (s : Set α) (hfinite : μ s ≠ ∞)
    (θ : α → ℝ) (b C : ℝ) (R : α → V)
    (hR : ∀ᵐ q ∂μ.restrict s, ‖R q‖ ≤ C) :
    ‖∫ q in s, shiftedFourierFactor (θ q) b • R q ∂μ‖ ≤
      μ.real s * C * Real.exp (-b) := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hfinite
  simpa only [measureReal_restrict_apply_univ] using
    norm_integral_shiftedFourier_le θ b C R hR

end FourierBound

section Ellipsoid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The admissible support point for the ellipsoid `‖Q β‖ ≤ ρ`, where
`P = Q⁻¹` is the symmetric inverse square-root metric. The formula also
handles zero directions, using the ordinary zero value of real division. -/
def ellipsoidSupportPoint (P : E →L[ℝ] E) (ρ : ℝ) (n : E) : E :=
  P ((ρ / ‖P n‖) • P n)

theorem ellipsoidSupportPoint_admissible
    (P Q : E →L[ℝ] E) (hQP : ∀ x, Q (P x) = x)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (n : E) :
    ‖Q (ellipsoidSupportPoint P ρ n)‖ ≤ ρ := by
  rw [ellipsoidSupportPoint, hQP]
  by_cases hn : P n = 0
  · simp [hn, hρ]
  · have hnorm : ‖P n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ (norm_nonneg _)),
      div_mul_cancel₀ ρ hnorm]

/-- The explicitly constructed shift attains the dual ellipsoid norm. -/
theorem ellipsoidSupportPoint_pairing
    (P : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (ρ : ℝ) (n : E) :
    ⟪ellipsoidSupportPoint P ρ n, n⟫_ℝ = ρ * ‖P n‖ := by
  rw [ellipsoidSupportPoint, hsym, real_inner_smul_self_left]
  by_cases hn : ‖P n‖ = 0
  · simp [hn]
  · field_simp

/-- Cauchy--Schwarz proves maximality over the whole admissible ellipsoid. -/
theorem ellipsoid_pairing_le
    (P Q : E →L[ℝ] E) (hPQ : ∀ x, P (Q x) = x)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (ρ : ℝ) (β n : E) (hβ : ‖Q β‖ ≤ ρ) :
    ⟪β, n⟫_ℝ ≤ ρ * ‖P n‖ := by
  calc
    ⟪β, n⟫_ℝ = ⟪Q β, P n⟫_ℝ := by rw [← hsym, hPQ]
    _ ≤ ‖Q β‖ * ‖P n‖ := real_inner_le_norm _ _
    _ ≤ ρ * ‖P n‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)

/-- The ellipsoid support value is attained, with both the maximizer and
the universal upper bound proved from inverse-metric identities. -/
theorem ellipsoid_support_maximum
    (P Q : E →L[ℝ] E)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (n : E) :
    ∃ β : E, ‖Q β‖ ≤ ρ ∧ ⟪β, n⟫_ℝ = ρ * ‖P n‖ ∧
      ∀ γ : E, ‖Q γ‖ ≤ ρ → ⟪γ, n⟫_ℝ ≤ ⟪β, n⟫_ℝ := by
  refine ⟨ellipsoidSupportPoint P ρ n,
    ellipsoidSupportPoint_admissible P Q hQP ρ hρ n,
    ellipsoidSupportPoint_pairing P hsym ρ n, ?_⟩
  intro γ hγ
  rw [ellipsoidSupportPoint_pairing P hsym]
  exact ellipsoid_pairing_le P Q hPQ hsym ρ γ n hγ

end Ellipsoid

section OptimizedBound

variable {α E V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- Full-block exponential upper bound in the inverse square-root metric.
The premise `hshift` is the explicit shifted Fourier representation supplied
by contour deformation; the exponential estimate and optimizing shift are
derived here rather than assumed. -/
theorem full_block_exponential_upper
    (P Q : E →L[ℝ] E) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (n : E) (θ : α → ℝ)
    (R : E → α → V) (C : ℝ) (G : V)
    (hshift : ∀ β, ‖Q β‖ ≤ ρ →
      G = ∫ q, shiftedFourierFactor (θ q) ⟪β, n⟫_ℝ • R β q ∂μ)
    (hR : ∀ β, ‖Q β‖ ≤ ρ → ∀ᵐ q ∂μ, ‖R β q‖ ≤ C) :
    ‖G‖ ≤ μ.real univ * C * Real.exp (-ρ * ‖P n‖) := by
  let β := ellipsoidSupportPoint P ρ n
  have hβ : ‖Q β‖ ≤ ρ := ellipsoidSupportPoint_admissible P Q hQP ρ hρ n
  rw [hshift β hβ]
  have h := norm_integral_shiftedFourier_le θ ⟪β, n⟫_ℝ C (R β) (hR β hβ)
  have hpair : ⟪β, n⟫_ℝ = ρ * ‖P n‖ := ellipsoidSupportPoint_pairing P hsym ρ n
  rw [hpair] at h ⊢
  simpa only [neg_mul] using h

end OptimizedBound

end Maxwell.Green
