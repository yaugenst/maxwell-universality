import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Maxwell.Spectral

open scoped ComplexConjugate
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- An exact diagonal representation gives the corresponding weighted quadratic form. -/
theorem diagonal_quadratic_form {ι : Type*} [Fintype ι] {T : E →ₗ[ℂ] E}
    (b : OrthonormalBasis ι ℂ E) (μ : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (μ i : ℂ) * b.repr x i) (x : E) :
    Complex.re (inner ℂ x (T x)) = ∑ i, μ i * ‖b.repr x i‖ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← b.repr_apply_apply, hdiag]
  rw [b.repr_apply_apply]
  rw [← mul_assoc, mul_comm (inner ℂ x (b i))]
  rw [mul_assoc, Complex.mul_re]
  change μ i * (inner ℂ x (b i) * inner ℂ (b i) x).re -
    0 * (inner ℂ x (b i) * inner ℂ (b i) x).im = _
  simp only [zero_mul, sub_zero]
  congr 1
  change RCLike.re (inner ℂ x (b i) * inner ℂ (b i) x) = _
  rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply, norm_star, pow_two]

/-- The quadratic form in the spectral theorem's orthonormal coordinates. -/
theorem spectral_quadratic_form {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (x : E) :
    Complex.re (inner ℂ x (T x)) =
      ∑ i, hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 :=
  diagonal_quadratic_form (hT.eigenvectorBasis rfl) (hT.eigenvalues rfl)
    (hT.eigenvectorBasis_apply_self_apply rfl) x

omit [FiniteDimensional ℂ E] in
/-- A diagonal quadratic form need not be listed in sorted order: its coercivity
on a trial subspace bounds the number of diagonal weights above the threshold. -/
theorem quadratic_minmax_count {ι : Type*} [Fintype ι]
    {T : E →ₗ[ℂ] E} (b : OrthonormalBasis ι ℂ E) (μ : ι → ℝ)
    (hquad : ∀ x : E, Complex.re (inner ℂ x (T x)) = ∑ i, μ i * ‖b.repr x i‖ ^ 2)
    (W : Submodule ℂ E) (c : ℝ)
    (hW : ∀ x : W, c * ‖(x : E)‖ ^ 2 ≤ Complex.re (inner ℂ (x : E) (T x))) :
    Module.finrank ℂ W ≤ (Finset.univ.filter fun i => c ≤ μ i).card := by
  classical
  let high := {i : ι // c ≤ μ i}
  let f : W →ₗ[ℂ] (high → ℂ) :=
    { toFun := fun x i => b.repr (x : E) i
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hhigh (i : ι) (hi : c ≤ μ i) :
        b.repr (x : E) i = 0 := by
      exact congrFun hx (⟨i, hi⟩ : high)
    have hterm (i : ι) :
        (μ i - c) * ‖b.repr (x : E) i‖ ^ 2 ≤ 0 := by
      by_cases hi : c ≤ μ i
      · rw [hhigh i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hi))
          (sq_nonneg _)
    have hnorm : ∑ i, ‖b.repr (x : E) i‖ ^ 2 = ‖(x : E)‖ ^ 2 := by
      simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right (x : E)
    have hsum : ∑ i, (μ i - c) * ‖b.repr (x : E) i‖ ^ 2 = 0 := by
      apply le_antisymm (Finset.sum_nonpos fun i _ => hterm i)
      have h := hW x
      rw [hquad] at h
      simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm] using
        sub_nonneg.mpr h
    have hzero (i : ι) : b.repr (x : E) i = 0 := by
      by_cases hi : c ≤ μ i
      · exact hhigh i hi
      · have ht := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterm i)).mp hsum i
          (Finset.mem_univ i)
        have he : μ i - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt (lt_of_not_ge hi))
        have hn := (mul_eq_zero.mp ht).resolve_left he
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    apply Subtype.ext
    apply b.repr.injective
    ext i
    simpa using hzero i
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa [high, Fintype.card_subtype] using hd


/-- A trial subspace bounded below by `c` forces at least its dimension of
spectral eigenvalues (including multiplicity) to lie at or above `c`. -/
theorem finrank_le_card_eigenvalues_ge {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (W : Submodule ℂ E) (c : ℝ)
    (hW : ∀ x : W, c * ‖(x : E)‖ ^ 2 ≤ Complex.re (inner ℂ (x : E) (T x))) :
    Module.finrank ℂ W ≤
      (Finset.univ.filter fun i => c ≤ hT.eigenvalues rfl i).card :=
  quadratic_minmax_count (hT.eigenvectorBasis rfl) (hT.eigenvalues rfl)
    (spectral_quadratic_form hT) W c hW

/-- Saturating an upper bound on an eligible index set exhausts that set. -/
theorem eq_of_subset_of_card_bounds {ι : Type*} {above eligible : Finset ι} {k : ℕ}
    (hsub : above ⊆ eligible) (hsmall : eligible.card ≤ k) (hlarge : k ≤ above.card) :
    above = eligible :=
  Finset.eq_of_subset_of_card_le hsub (hsmall.trans hlarge)

omit [FiniteDimensional ℂ E] in
/-- If the eligible spectrum contains at most `k` indices, and a trial space of
dimension at least `k` satisfies the bound, every eligible index satisfies it.
For the two-band argument, use `k = 2` and eligibility `0 < λ i ∧ λ i < b`. -/
theorem quadratic_minmax_saturates {ι : Type*} [Fintype ι]
    {T : E →ₗ[ℂ] E} (b : OrthonormalBasis ι ℂ E) (μ : ι → ℝ)
    (hquad : ∀ x : E, Complex.re (inner ℂ x (T x)) = ∑ i, μ i * ‖b.repr x i‖ ^ 2)
    (W : Submodule ℂ E) (c : ℝ) (eligible : Finset ι) (k : ℕ)
    (hW : ∀ x : W, c * ‖(x : E)‖ ^ 2 ≤ Complex.re (inner ℂ (x : E) (T x)))
    (hsub : ∀ i, c ≤ μ i → i ∈ eligible)
    (hsmall : eligible.card ≤ k) (hlarge : k ≤ Module.finrank ℂ W) :
    ∀ i ∈ eligible, c ≤ μ i := by
  classical
  have hc := quadratic_minmax_count b μ hquad W c hW
  have heq : (Finset.univ.filter fun i => c ≤ μ i) = eligible :=
    eq_of_subset_of_card_bounds (fun i hi => hsub i (Finset.mem_filter.mp hi).2)
      hsmall (hlarge.trans hc)
  intro i hi
  rw [← heq] at hi
  exact (Finset.mem_filter.mp hi).2

end Maxwell.Spectral
