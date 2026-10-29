import Maxwell.Spectral.LowHighInertia
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Maxwell.Spectral.BoxSchur

noncomputable section

/-- Completing the high-variable square gives precisely the two diagonal
losses and the mixed geometric-mean loss used by the box verifier. -/
theorem three_block_positive (a b c α β x y z : ℝ)
    (hc : 0 ≤ c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 0 < a-α^2) (hg : 0 < b-β^2)
    (hdet : (c+α*β)^2 < (a-α^2)*(b-β^2))
    (hx : 0 ≤ x) (hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < a*x^2+b*y^2+z^2-2*c*x*y-2*α*x*z-2*β*y*z := by
  by_cases hxy : x ≠ 0 ∨ y ≠ 0
  · have h := positive_low_high_quadratic hp hg
      (add_nonneg hc (mul_nonneg hα hβ)) hdet hx hy hxy
    nlinarith [sq_nonneg (z-α*x-β*y)]
  · push Not at hxy
    rcases hxy with ⟨rfl, rfl⟩
    have hz0 : z ≠ 0 := by simpa using hne
    simpa using sq_pos_of_ne_zero hz0

variable {H P G K W : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup P] [NormedSpace ℂ P]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]
variable [NormedAddCommGroup K] [NormedSpace ℂ K]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A weighted high-space estimate is sufficient; no uniform replacement
by the smallest high eigenvalue is made. This retains the sharp bounds
accepted by the finite certificate. -/
theorem positive_three_block_trial
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (F : P →ₗ[ℂ] H) (L : G →ₗ[ℂ] H) (Q : K →ₗ[ℂ] H)
    (Z : K →ₗ[ℂ] W) (hZ : Function.Injective Z)
    (a b c α β : ℝ) (hc : 0 ≤ c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 0 < a-α^2) (hg : 0 < b-β^2)
    (hdet : (c+α*β)^2 < (a-α^2)*(b-β^2))
    (hF : ∀ p, a*‖p‖^2 ≤ (inner ℂ (F p) (A (F p))).re)
    (hL : ∀ g, b*‖g‖^2 ≤ (inner ℂ (L g) (A (L g))).re)
    (hQ : ∀ k, ‖Z k‖^2 ≤ (inner ℂ (Q k) (A (Q k))).re)
    (hFL : ∀ p g, |(inner ℂ (F p) (A (L g))).re| ≤ c*‖p‖*‖g‖)
    (hFQ : ∀ p k, |(inner ℂ (F p) (A (Q k))).re| ≤ α*‖p‖*‖Z k‖)
    (hLQ : ∀ g k, |(inner ℂ (L g) (A (Q k))).re| ≤ β*‖g‖*‖Z k‖)
    (v : P × (G × K)) (hv : v ≠ 0) :
    0 < (inner ℂ (F v.1+L v.2.1+Q v.2.2)
      (A (F v.1+L v.2.1+Q v.2.2))).re := by
  have hne : ‖v.1‖ ≠ 0 ∨ ‖v.2.1‖ ≠ 0 ∨ ‖Z v.2.2‖ ≠ 0 := by
    by_contra h
    push Not at h
    have hk : v.2.2 = 0 := hZ (by simpa using norm_eq_zero.mp h.2.2)
    exact hv (Prod.ext (norm_eq_zero.mp h.1) (Prod.ext (norm_eq_zero.mp h.2.1) hk))
  have h := three_block_positive a b c α β ‖v.1‖ ‖v.2.1‖ ‖Z v.2.2‖
    hc hα hβ hp hg hdet (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hne
  have hsym (u w : H) : (inner ℂ w (A u)).re = (inner ℂ u (A w)).re := by
    rw [← hA w u]
    exact inner_re_symm (𝕜 := ℂ) (A w) u
  have h₁ := (abs_le.mp (hFL v.1 v.2.1)).1
  have h₂ := (abs_le.mp (hFQ v.1 v.2.2)).1
  have h₃ := (abs_le.mp (hLQ v.2.1 v.2.2)).1
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
  rw [hsym (F v.1) (L v.2.1), hsym (F v.1) (Q v.2.2),
    hsym (L v.2.1) (Q v.2.2)]
  linarith [hF v.1, hL v.2.1, hQ v.2.2]

/-- The accepted positive/gradient/high block and negative trial space
determine all signs of the full matrix, including absence of zero modes. -/
theorem inertia_of_box_trials
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ P] [FiniteDimensional ℂ G]
    [FiniteDimensional ℂ K]
    {N : Type*} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (Fneg : N →ₗ[ℂ] H) (F : P →ₗ[ℂ] H) (L : G →ₗ[ℂ] H) (Q : K →ₗ[ℂ] H)
    (Z : K →ₗ[ℂ] W) (hZ : Function.Injective Z)
    (a b c α β : ℝ) (hc : 0 ≤ c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 0 < a-α^2) (hg : 0 < b-β^2)
    (hdet : (c+α*β)^2 < (a-α^2)*(b-β^2))
    (hneg : ∀ n, n ≠ 0 → (inner ℂ (Fneg n) (A (Fneg n))).re < 0)
    (hF : ∀ p, a*‖p‖^2 ≤ (inner ℂ (F p) (A (F p))).re)
    (hL : ∀ g, b*‖g‖^2 ≤ (inner ℂ (L g) (A (L g))).re)
    (hQ : ∀ k, ‖Z k‖^2 ≤ (inner ℂ (Q k) (A (Q k))).re)
    (hFL : ∀ p g, |(inner ℂ (F p) (A (L g))).re| ≤ c*‖p‖*‖g‖)
    (hFQ : ∀ p k, |(inner ℂ (F p) (A (Q k))).re| ≤ α*‖p‖*‖Z k‖)
    (hLQ : ∀ g k, |(inner ℂ (L g) (A (Q k))).re| ≤ β*‖g‖*‖Z k‖)
    (hdim : Module.finrank ℂ N +
      (Module.finrank ℂ P + (Module.finrank ℂ G+Module.finrank ℂ K)) = Module.finrank ℂ H) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card = Module.finrank ℂ N ∧
    (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card = 0 ∧
    (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card =
      Module.finrank ℂ P+(Module.finrank ℂ G+Module.finrank ℂ K) := by
  let T := F.coprod (L.coprod Q)
  have hT : ∀ v, v ≠ 0 → 0 < (inner ℂ (T v) (A (T v))).re := by
    simpa only [T, LinearMap.coprod_apply, add_assoc] using
      positive_three_block_trial A hA F L Q Z hZ a b c α β hc hα hβ hp hg hdet
        hF hL hQ hFL hFQ hLQ
  simpa only [Module.finrank_prod] using
    inertia_of_complementary_trials A hA Fneg T hneg hT (by
      simpa only [Module.finrank_prod] using hdim)

end
end Maxwell.Spectral.BoxSchur
