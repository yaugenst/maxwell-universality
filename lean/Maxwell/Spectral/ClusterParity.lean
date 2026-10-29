import Maxwell.Spectral.ClusterInverse

namespace Maxwell.Spectral.ClusterInverse

noncomputable section

open ClusterProjection

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem projection_zero_of_opposite_parity (b : OrthonormalBasis ι ℂ H) (S : Finset ι)
    (I : H ≃ₗᵢ[ℂ] H) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hS : ∀ i ∈ S, I (b i) = σ • b i) (v : H) (hv : I v = (-σ) • v) :
    projection b S v = 0 := by
  apply b.repr.injective
  ext i
  simp only [repr_projection, map_zero, PiLp.zero_apply]
  by_cases hi : i ∈ S
  · simp only [hi, ite_true, b.repr_apply_apply]
    have h := I.inner_map_map (b i) v
    rw [hS i hi, hv] at h
    rcases hσ with rfl | rfl
    · simp only [one_smul, neg_one_smul, inner_neg_right] at h
      have hh : (2 : ℂ) * inner ℂ (b i) v = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    · simp only [neg_neg, one_smul, neg_one_smul, inner_neg_left] at h
      have hh : (2 : ℂ) * inner ℂ (b i) v = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  · simp [hi]

theorem projection_symmetry_zero (b : OrthonormalBasis ι ℂ H) (S : Finset ι)
    (I : H ≃ₗᵢ[ℂ] H) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hS : ∀ i ∈ S, I (b i) = σ • b i) (v : H) (hv : projection b S v = 0) :
    projection b S (I v) = 0 := by
  apply b.repr.injective
  ext i
  simp only [repr_projection, map_zero, PiLp.zero_apply]
  by_cases hi : i ∈ S
  · simp only [hi, ite_true, b.repr_apply_apply]
    have hz := congrArg (fun x : H => b.repr x i) hv
    rw [repr_projection] at hz
    simp only [hi, ite_true, map_zero, PiLp.zero_apply] at hz
    rw [b.repr_apply_apply] at hz
    have h := I.inner_map_map (b i) v
    rw [hS i hi, hz] at h
    rcases hσ with rfl | rfl
    · simpa only [one_smul] using h
    · simpa only [neg_one_smul, inner_neg_left, neg_eq_zero] using h
  · simp [hi]

theorem complement_kernel (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - E|) (v : H)
    (hP : projection b S v = 0) (hzero : T v - (E : ℂ) • v = 0) : v = 0 := by
  have h := projection_error_norm b T μ hdiag S E g hg hgap v
  rw [hP, sub_zero, hzero, norm_zero, zero_div] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- The exact reduced-inverse corrector has the parity opposite to the
cluster, derived from the physical operator's symmetry and uniqueness. -/
theorem reducedInverse_opposite_parity (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - E|)
    (I : H ≃ₗᵢ[ℂ] H) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hS : ∀ i ∈ S, I (b i) = σ • b i)
    (hcommute : ∀ x, T (I x) = I (T x)) (v : H) (hv : I v = (-σ) • v) :
    I (reducedInverse b μ S E v) = (-σ) • reducedInverse b μ S E v := by
  let y := reducedInverse b μ S E v
  have hy : projection b S y = 0 :=
    congrArg (fun L : H →L[ℂ] H => L v) (projection_reducedInverse b μ S E)
  have hsep (i : ι) (hi : i ∉ S) : μ i ≠ E := by
    intro he
    have hh := hgap i hi
    rw [he, sub_self, abs_zero] at hh
    linarith
  have hsolve : T y - (E : ℂ) • y = v :=
    solve_complement b T μ hdiag S E hsep v
      (projection_zero_of_opposite_parity b S I σ hσ hS v hv)
  have hTy : T y = v + (E : ℂ) • y := (sub_eq_iff_eq_add).mp hsolve
  have hz : I y + σ • y = 0 := by
    apply complement_kernel b T μ hdiag S E g hg hgap
    · rw [map_add, map_smul, hy, smul_zero,
        projection_symmetry_zero b S I σ hσ hS y hy, zero_add]
    · rw [map_add, map_smul, hcommute, hTy, I.map_add, I.map_smul, hv]
      module
  change I y = (-σ) • y
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left hz

end
end Maxwell.Spectral.ClusterInverse
