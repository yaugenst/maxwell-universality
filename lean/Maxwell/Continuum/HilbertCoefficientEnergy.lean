import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith

/-! Energy inequalities from actual Hilbert-basis coefficients. The basis
need not itself consist of eigenvectors: a coefficient identity on the
field under consideration suffices. -/

noncomputable section

namespace Maxwell.Continuum.HilbertCoefficientEnergy

set_option backward.isDefEq.respectTransparency false

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (b : HilbertBasis ι ℂ H)

theorem hasSum_energy (u v : H) :
    HasSum (fun i => (inner ℂ (b.repr u i) (b.repr v i)).re) (inner ℂ u v).re := by
  simpa only [Complex.reCLM_apply, b.repr.inner_map_map] using
    Complex.reCLM.hasSum (lp.hasSum_inner (b.repr u) (b.repr v))

theorem hasSum_norm_sq (u : H) :
    HasSum (fun i => ‖b.repr u i‖ ^ 2) (‖u‖ ^ 2) := by
  convert! hasSum_energy b u u using 1
  · funext i
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (b.repr u i)).symm
  · exact (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm

theorem coefficient_energy (z : ℂ) (ell : ℝ) :
    (inner ℂ z ((ell : ℂ) • z)).re = ell * ‖z‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Parseval and the actual coefficient equation give a quadratic lower
bound, even if the component basis does not diagonalize every vector. -/
theorem energy_lower (u v : H) (ell : ι → ℝ) (c : ℝ)
    (hcoeff : ∀ i, b.repr v i = (ell i : ℂ) • b.repr u i)
    (hhigh : ∀ i, b.repr u i ≠ 0 → c ≤ ell i) :
    c * ‖u‖ ^ 2 ≤ (inner ℂ u v).re := by
  apply hasSum_le _ ((hasSum_norm_sq b u).mul_left c) (hasSum_energy b u v)
  intro i
  rw [hcoeff i, coefficient_energy]
  by_cases hi : b.repr u i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_right (hhigh i hi) (sq_nonneg _)

def modeSpan (s : Set ι) : Submodule ℂ H := Submodule.span ℂ (b '' s)

theorem coefficient_zero_of_orthogonal (s : Set ι) (u : H)
    (hu : u ∈ (modeSpan b s)ᗮ) (i : ι) (hi : i ∈ s) : b.repr u i = 0 := by
  rw [b.repr_apply_apply]
  exact hu (b i) (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- All low coefficients vanish on the orthogonal complement of their
closed span. This is the high-mode estimate used before the second Schur
elimination. -/
theorem energy_lower_of_orthogonal (s : Set ι) (u v : H) (ell : ι → ℝ) (c : ℝ)
    (hcoeff : ∀ i, b.repr v i = (ell i : ℂ) • b.repr u i)
    (hcut : ∀ i ∉ s, c ≤ ell i) (hu : u ∈ (modeSpan b s)ᗮ) :
    c * ‖u‖ ^ 2 ≤ (inner ℂ u v).re := by
  apply energy_lower b u v ell c hcoeff
  intro i hi
  exact hcut i (fun his => hi (coefficient_zero_of_orthogonal b s u hu i his))

end Maxwell.Continuum.HilbertCoefficientEnergy
