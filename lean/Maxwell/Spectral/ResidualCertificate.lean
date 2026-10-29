import Maxwell.Spectral.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Maxwell.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The exact residual norm in a selfadjoint operator's orthonormal
eigenbasis. This connects finite rational residual witnesses to actual
eigenvalues, without assuming an eigenpair near the proposed center. -/
theorem shifted_norm_sq_spectral (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (c : ℝ) (u : H) :
    ‖T u - (c : ℂ) • u‖ ^ 2 =
      ∑ i, (hT.eigenvalues rfl i - c) ^ 2 *
        ‖(hT.eigenvectorBasis rfl).repr u i‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  have hnorm : ∑ i, ‖b.repr (T u - (c : ℂ) • u) i‖ ^ 2 =
      ‖T u - (c : ℂ) • u‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using
      b.sum_sq_norm_inner_right (T u - (c : ℂ) • u)
  rw [← hnorm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.repr (T u - (c : ℂ) • u) i =
      ((hT.eigenvalues rfl i - c : ℝ) : ℂ) * b.repr u i := by
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      b, hT.eigenvectorBasis_apply_self_apply, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sub]
    ring
  rw [hi, norm_mul, mul_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem exists_eigenvalue_near_of_residual_sq (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (u : H) (hu : u ≠ 0) (c r : ℝ) (hr : 0 ≤ r)
    (hres : ‖T u - (c : ℂ) • u‖ ^ 2 ≤ r ^ 2 * ‖u‖ ^ 2) :
    ∃ i : Fin (Module.finrank ℂ H), |hT.eigenvalues rfl i - c| ≤ r := by
  classical
  by_contra hnone
  push Not at hnone
  let b := hT.eigenvectorBasis rfl
  have hnorm : ∑ i, ‖b.repr u i‖ ^ 2 = ‖u‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right u
  have hnonzero : ∃ i, b.repr u i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hnonzero
  have hgap (j : Fin (Module.finrank ℂ H)) : r ^ 2 < (hT.eigenvalues rfl j - c) ^ 2 := by
    have hj := hnone j
    nlinarith only [hj, hr, sq_abs (hT.eigenvalues rfl j - c),
      abs_nonneg (hT.eigenvalues rfl j - c)]
  have hsum : ∑ j, r ^ 2 * ‖b.repr u j‖ ^ 2 <
      ∑ j, (hT.eigenvalues rfl j - c) ^ 2 * ‖b.repr u j‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_le_mul_of_nonneg_right (hgap j).le (sq_nonneg _)
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      exact mul_lt_mul_of_pos_right (hgap i) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi))
  rw [← Finset.mul_sum, hnorm] at hsum
  rw [shifted_norm_sq_spectral T hT c u] at hres
  exact (not_lt_of_ge hres) hsum

theorem two_distinct_eigenvalues_of_disjoint_residuals
    (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (u v : H) (hu : u ≠ 0) (hv : v ≠ 0) (c d r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hsep : c + r < d - s)
    (huRes : ‖T u - (c : ℂ) • u‖ ^ 2 ≤ r ^ 2 * ‖u‖ ^ 2)
    (hvRes : ‖T v - (d : ℂ) • v‖ ^ 2 ≤ s ^ 2 * ‖v‖ ^ 2) :
    ∃ i j : Fin (Module.finrank ℂ H), i ≠ j ∧
      |hT.eigenvalues rfl i - c| ≤ r ∧ |hT.eigenvalues rfl j - d| ≤ s := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_near_of_residual_sq T hT u hu c r hr huRes
  obtain ⟨j, hj⟩ := exists_eigenvalue_near_of_residual_sq T hT v hv d s hs hvRes
  refine ⟨i, j, ?_, hi, hj⟩
  intro heq
  subst j
  have hi' := (abs_le.mp hi).2
  have hj' := (abs_le.mp hj).1
  linarith

end Maxwell.Spectral
