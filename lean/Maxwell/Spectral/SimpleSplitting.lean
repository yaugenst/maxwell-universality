import Maxwell.Spectral.MinMax
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace Maxwell.Spectral.SimpleSplitting

noncomputable section

open scoped ComplexConjugate

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

abbrev Complement (i : ι) := EuclideanSpace ℂ {j : ι // j ≠ i}

/-- Separate one spectral coordinate from all the others. -/
def coordinateSplit (i : ι) : EuclideanSpace ℂ ι ≃ₗ[ℂ] ℂ × Complement i where
  toFun x := (x i, WithLp.toLp 2 fun j => x j)
  invFun x := WithLp.toLp 2 fun j => if h : j = i then x.1 else x.2 ⟨j, h⟩
  left_inv x := by
    ext j
    change (if h : j = i then x i else x j) = x j
    split_ifs with h <;> simp [h]
  right_inv x := by
    apply Prod.ext
    · simp
    · ext j
      simp [j.property]
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The concrete direct-sum coordinate map supplied by an orthonormal basis. -/
def decomposition (b : OrthonormalBasis ι ℂ H) (i : ι) :
    (ℂ × Complement i) ≃L[ℂ] H :=
  ((coordinateSplit i).symm.trans b.repr.symm.toLinearEquiv).toContinuousLinearEquiv

omit [FiniteDimensional ℂ H] in
@[simp] theorem decomposition_repr (b : OrthonormalBasis ι ℂ H) (i j : ι)
    (z : ℂ × Complement i) :
    b.repr (decomposition b i z) j = if h : j = i then z.1 else z.2 ⟨j, h⟩ := by
  change b.repr (b.repr.symm ((coordinateSplit i).symm z)) j = _
  rw [b.repr.apply_symm_apply]
  rfl

omit [FiniteDimensional ℂ H] in
@[simp] theorem decomposition_one_zero (b : OrthonormalBasis ι ℂ H) (i : ι) :
    decomposition b i (1, 0) = b i := by
  apply b.repr.injective
  ext j
  rw [decomposition_repr, b.repr_self]
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

omit [FiniteDimensional ℂ H] in
@[simp] theorem decomposition_symm_fst (b : OrthonormalBasis ι ℂ H) (i : ι) (x : H) :
    ((decomposition b i).symm x).1 = inner ℂ (b i) x := by
  change b.repr x i = _
  exact b.repr_apply_apply x i

omit [FiniteDimensional ℂ H] in
theorem decomposition_norm_sq (b : OrthonormalBasis ι ℂ H) (i : ι)
    (z : ℂ × Complement i) :
    ‖decomposition b i z‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : ι => j = i)]
  congr 1
  · rw [Finset.sum_eq_single (⟨i, rfl⟩ : {j : ι // j = i})]
    · simp [decomposition_repr]
    · intro j _ hj
      exact (hj (Subtype.ext j.property)).elim
    · intro h
      simp only [Finset.mem_univ, not_true_eq_false] at h
  · rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp [decomposition_repr, j.property]

/-- The shifted complementary block is an explicit real diagonal operator. -/
def diagonalComplement (μ : ι → ℝ) (i : ι) : Complement i →L[ℂ] Complement i :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun j => ((μ j - μ i : ℝ) : ℂ) * v j
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }

@[simp] theorem diagonalComplement_apply (μ : ι → ℝ) (i : ι) (v : Complement i)
    (j : {j : ι // j ≠ i}) :
    diagonalComplement μ i v j = ((μ j - μ i : ℝ) : ℂ) * v j := rfl

theorem diagonalComplement_injective (μ : ι → ℝ) (i : ι)
    (hsimple : ∀ j, j ≠ i → μ j ≠ μ i) :
    Function.Injective (diagonalComplement μ i) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  ext j
  have h := congrArg (fun x : Complement i => x j) hv
  change ((μ j - μ i : ℝ) : ℂ) * v j = 0 at h
  have hn : ((μ j - μ i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (hsimple j j.property)
  exact (mul_eq_zero.mp h).resolve_left hn

/-- A simple real diagonal value supplies a genuine complementary inverse. -/
def complementaryEquiv (μ : ι → ℝ) (i : ι)
    (hsimple : ∀ j, j ≠ i → μ j ≠ μ i) : Complement i ≃L[ℂ] Complement i :=
  ContinuousLinearEquiv.ofBijective (diagonalComplement μ i)
    (LinearMap.ker_eq_bot.mpr (diagonalComplement_injective μ i hsimple))
    (LinearMap.range_eq_top.mpr
      ((diagonalComplement μ i).toLinearMap.injective_iff_surjective.mp
        (diagonalComplement_injective μ i hsimple)))

omit [FiniteDimensional ℂ H] in
/-- Exact spectral coordinates put a simple eigenvalue in the form required
by the analytic implicit-function construction. -/
theorem operator_decomposition (T : H →ₗ[ℂ] H) (b : OrthonormalBasis ι ℂ H)
    (μ : ι → ℝ) (hdiag : ∀ x j, b.repr (T x) j = (μ j : ℂ) * b.repr x j)
    (i : ι) (z : ℂ × Complement i) :
    T (decomposition b i z) =
      decomposition b i ((μ i : ℂ) * z.1, (μ i : ℂ) • z.2 + diagonalComplement μ i z.2) := by
  apply b.repr.injective
  ext j
  rw [hdiag, decomposition_repr, decomposition_repr]
  split_ifs with h
  · subst j
    rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, diagonalComplement_apply,
      Complex.ofReal_sub]
    ring

theorem diagonalComplement_norm_lower (μ : ι → ℝ) (i : ι) (g : ℝ) (hg : 0 ≤ g)
    (hgap : ∀ j, j ≠ i → g ≤ |μ j - μ i|) (v : Complement i) :
    g * ‖v‖ ≤ ‖diagonalComplement μ i v‖ := by
  have hs : g ^ 2 * ‖v‖ ^ 2 ≤ ‖diagonalComplement μ i v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [diagonalComplement_apply, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hj := hgap j j.property
    have hj2 : g ^ 2 ≤ (μ j - μ i) ^ 2 := by
      nlinarith only [hj, hg, abs_nonneg (μ j - μ i), sq_abs (μ j - μ i)]
    exact mul_le_mul_of_nonneg_right hj2 (sq_nonneg _)
  have hn := norm_nonneg v
  have hd := norm_nonneg (diagonalComplement μ i v)
  nlinarith only [hs, mul_nonneg hg hn, hd]

/-- The inverse complementary block has the quantitative norm required for
the reduced resolvent and corrector construction. -/
theorem complementaryEquiv_symm_norm_le (μ : ι → ℝ) (i : ι)
    (hsimple : ∀ j, j ≠ i → μ j ≠ μ i)
    (g : ℝ) (hg : 0 < g) (hgap : ∀ j, j ≠ i → g ≤ |μ j - μ i|) :
    ‖(complementaryEquiv μ i hsimple).symm.toContinuousLinearMap‖ ≤ g⁻¹ := by
  apply (complementaryEquiv μ i hsimple).symm.toContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr hg.le)
  intro v
  have h := diagonalComplement_norm_lower μ i g hg.le hgap
    ((complementaryEquiv μ i hsimple).symm v)
  have he : diagonalComplement μ i ((complementaryEquiv μ i hsimple).symm v) = v :=
    (complementaryEquiv μ i hsimple).apply_symm_apply v
  rw [he] at h
  change ‖(complementaryEquiv μ i hsimple).symm v‖ ≤ g⁻¹ * ‖v‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hg).mpr (by nlinarith only [h])

theorem spectral_decomposition (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H)) (z : ℂ × Complement i) :
    T (decomposition (hT.eigenvectorBasis rfl) i z) =
      decomposition (hT.eigenvectorBasis rfl) i
        ((hT.eigenvalues rfl i : ℂ) * z.1,
          (hT.eigenvalues rfl i : ℂ) • z.2 + diagonalComplement (hT.eigenvalues rfl) i z.2) :=
  operator_decomposition T (hT.eigenvectorBasis rfl) (hT.eigenvalues rfl)
    (hT.eigenvectorBasis_apply_self_apply rfl) i z

theorem simple_complement_kernel (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H))
    (hsimple : ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i)
    (v : H) (horth : inner ℂ (hT.eigenvectorBasis rfl i) v = 0)
    (hker : T v - (hT.eigenvalues rfl i : ℂ) • v = 0) : v = 0 := by
  let b := hT.eigenvectorBasis rfl
  apply b.repr.injective
  ext j
  simp only [map_zero, PiLp.zero_apply]
  by_cases hj : j = i
  · subst j
    simpa only [b, OrthonormalBasis.repr_apply_apply] using horth
  · have he := congrArg (fun x : H => b.repr x j) (sub_eq_zero.mp hker)
    simp only [b, hT.eigenvectorBasis_apply_self_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal] at he
    have hne : (hT.eigenvalues rfl j : ℂ) ≠ (hT.eigenvalues rfl i : ℂ) := by
      exact_mod_cast hsimple j hj
    have hz : ((hT.eigenvalues rfl j : ℂ) - (hT.eigenvalues rfl i : ℂ)) *
        b.repr v j = 0 := by
      change ((_ : ℂ) - _) * (hT.eigenvectorBasis rfl).repr v j = 0
      linear_combination he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end
end Maxwell.Spectral.SimpleSplitting
