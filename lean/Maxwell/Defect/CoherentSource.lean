import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual finite Fourier-source coherence and eigenvector-variation bounds. -/

namespace Maxwell.Defect

theorem norm_unit_phase_sub_one_le (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin (θ / 2)‖ = 2 * |Real.sin (θ / 2)| := by simp [Real.norm_eq_abs]
    _ ≤ 2 * |θ / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |θ| := by rw [abs_div]; norm_num; ring

theorem positive_fourier_sum_coherence {ι : Type*} [Fintype ι]
    (weight phase : ι → ℝ) {radius : ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hphase : ∀ i, |phase i| ≤ radius) :
    ‖(∑ i, (weight i : ℂ) * Complex.exp (Complex.I * phase i)) -
      ((∑ i, weight i : ℝ) : ℂ)‖ ≤ radius * ∑ i, weight i := by
  have hid : (∑ i, (weight i : ℂ) * Complex.exp (Complex.I * phase i)) -
      ((∑ i, weight i : ℝ) : ℂ) =
      ∑ i, (weight i : ℂ) * (Complex.exp (Complex.I * phase i) - 1) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [hid]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, weight i * radius := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight i)]
      exact mul_le_mul_of_nonneg_left
        ((norm_unit_phase_sub_one_le (phase i)).trans (hphase i)) (hweight i)
    _ = radius * ∑ i, weight i := by rw [← Finset.sum_mul]; ring

theorem finite_fourier_source_norm {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (phase : ι → ℝ) (cellSource : ι → E) {bound : ℝ}
    (hsource : ∀ i, ‖cellSource i‖ ≤ bound) :
    ‖∑ i, Complex.exp (Complex.I * phase i) • cellSource i‖ ≤
      Fintype.card ι * bound := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, bound := by
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_smul, Complex.norm_exp_I_mul_ofReal] using hsource i
    _ = Fintype.card ι * bound := by simp

/-- Varying the local Bloch eigenvector adds its norm variation times the
finite-source norm; no uncontrolled sum over the lattice is involved. -/
theorem source_overlap_variation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (φ φ₀ source : E) (a : ℂ)
    {variation sourceBound phaseError : ℝ}
    (hvariation : ‖φ - φ₀‖ ≤ variation) (hsource : ‖source‖ ≤ sourceBound)
    (hphase : ‖inner ℂ φ₀ source - a‖ ≤ phaseError) :
    ‖inner ℂ φ source - a‖ ≤ variation * sourceBound + phaseError := by
  have hid : inner ℂ φ source - a =
      inner ℂ (φ - φ₀) source + (inner ℂ φ₀ source - a) := by
    rw [inner_sub_left]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hphase
  apply (norm_inner_le_norm _ _).trans
  exact mul_le_mul hvariation hsource (norm_nonneg source)
    ((norm_nonneg (φ - φ₀)).trans hvariation)

/-- The coherent-cube Fourier overlap estimate used before restricting to
the radius `r/L` ball. Each cell contributes a positive scalar weight and
a contractive source vector. -/
theorem cube_fourier_overlap_error {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ φ₀ : E) (cellSource : ι → E) (weight phase : ι → ℝ)
    {L q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hsource : ∀ i, ‖cellSource i‖ ≤ 1)
    (hweight : ∀ i, 0 ≤ weight i)
    (hinner : ∀ i, inner ℂ φ₀ (cellSource i) = (weight i : ℂ))
    (hphase : ∀ i, |phase i| ≤ 4 * L * q)
    (hcount : (Fintype.card ι : ℝ) ≤ 8 * L ^ 3)
    (hvariation : ‖φ - φ₀‖ ≤ C * q) :
    ‖inner ℂ φ (∑ i, Complex.exp (Complex.I * phase i) • cellSource i) -
      ((∑ i, weight i : ℝ) : ℂ)‖ ≤
        4 * L * q * (∑ i, weight i) + 8 * C * L ^ 3 * q := by
  let source := ∑ i, Complex.exp (Complex.I * phase i) • cellSource i
  have hsn : ‖source‖ ≤ (Fintype.card ι : ℝ) := by
    simpa [source] using finite_fourier_source_norm phase cellSource hsource
  have href : inner ℂ φ₀ source =
      ∑ i, (weight i : ℂ) * Complex.exp (Complex.I * phase i) := by
    simp [source, inner_sum, inner_smul_right, hinner, mul_comm]
  have hcoherent : ‖inner ℂ φ₀ source - ((∑ i, weight i : ℝ) : ℂ)‖ ≤
      (4 * L * q) * ∑ i, weight i := by
    rw [href]
    exact positive_fourier_sum_coherence weight phase hweight hphase
  have hov := source_overlap_variation φ φ₀ source ((∑ i, weight i : ℝ) : ℂ)
    hvariation hsn hcoherent
  have hcount' := mul_le_mul_of_nonneg_left hcount (mul_nonneg hC hq)
  exact hov.trans (by nlinarith)

end Maxwell.Defect
