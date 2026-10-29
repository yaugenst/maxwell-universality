import Maxwell.Spectral.MinMax
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual control of the exact spectral cluster projection

The projector is the finite sum of rank-one orthogonal eigenvector projectors.
A coefficientwise spectral gap bounds its complementary component directly by
the residual, including the corresponding operator-norm estimate for trial maps.
-/

namespace Maxwell.Spectral.ClusterProjection

noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The actual orthogonal projection onto the selected eigenbasis coordinates. -/
def projection (b : OrthonormalBasis ι ℂ E) (S : Finset ι) : E →L[ℂ] E :=
  ∑ i ∈ S, InnerProductSpace.rankOne ℂ (b i) (b i)

omit [DecidableEq ι] in
theorem projection_apply (b : OrthonormalBasis ι ℂ E) (S : Finset ι) (u : E) :
    projection b S u = ∑ i ∈ S, b.repr u i • b i := by
  simp only [projection, sum_apply, InnerProductSpace.rankOne_apply,
    OrthonormalBasis.repr_apply_apply]

@[simp]
theorem repr_projection (b : OrthonormalBasis ι ℂ E) (S : Finset ι) (u : E) (i : ι) :
    b.repr (projection b S u) i = if i ∈ S then b.repr u i else 0 := by
  rw [projection_apply]
  simp [map_sum, map_smul, OrthonormalBasis.repr_self, Pi.single_apply, mul_ite]

@[simp]
theorem projection_basis (b : OrthonormalBasis ι ℂ E) (S : Finset ι) (i : ι) :
    projection b S (b i) = if i ∈ S then b i else 0 := by
  rw [projection_apply]
  simp [OrthonormalBasis.repr_self, PiLp.single_apply, ite_smul]

/-- Its range is exactly the span of the selected eigenvectors. -/
theorem projection_range (b : OrthonormalBasis ι ℂ E) (S : Finset ι) :
    LinearMap.range (projection b S).toLinearMap =
      Submodule.span ℂ (b '' (S : Set ι)) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    rw [ContinuousLinearMap.coe_coe, projection_apply]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change i ∈ S at hi
    exact ⟨b i, by simp only [ContinuousLinearMap.coe_coe, projection_basis, hi, ite_true]⟩

theorem projection_idempotent (b : OrthonormalBasis ι ℂ E) (S : Finset ι) :
    (projection b S).comp (projection b S) = projection b S := by
  apply ContinuousLinearMap.ext
  intro u
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, repr_projection]
  split_ifs <;> rfl

theorem projection_error_orthogonal (b : OrthonormalBasis ι ℂ E)
    (S : Finset ι) (u v : E) :
    inner ℂ (projection b S u) (v - projection b S v) = 0 := by
  rw [← b.repr.inner_map_map, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [map_sub, PiLp.sub_apply, repr_projection]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem projection_selfAdjoint [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E) (S : Finset ι) : IsSelfAdjoint (projection b S) := by
  change star (projection b S) = projection b S
  simp only [projection, map_sum, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]

omit [DecidableEq ι] in
theorem norm_sq_eq_sum_repr (b : OrthonormalBasis ι ℂ E) (u : E) :
    ‖u‖ ^ 2 = ∑ i, ‖b.repr u i‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_sq_norm_inner_right u).symm

omit [DecidableEq ι] in
theorem residual_repr (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : ι → ℝ) (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (c : ℝ) (u : E) (i : ι) :
    b.repr (T u - (c : ℂ) • u) i = ((μ i - c : ℝ) : ℂ) * b.repr u i := by
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    hdiag, Complex.ofReal_sub, sub_mul]

/-- Squared elementary Davis--Kahan estimate, proved in the eigenbasis. -/
theorem projection_error_sq (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : ι → ℝ) (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (S : Finset ι) (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - c|) (u : E) :
    g ^ 2 * ‖u - projection b S u‖ ^ 2 ≤ ‖T u - (c : ℂ) • u‖ ^ 2 := by
  rw [norm_sq_eq_sum_repr b, norm_sq_eq_sum_repr b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [residual_repr b T μ hdiag]
  simp only [map_sub, PiLp.sub_apply, repr_projection]
  by_cases hi : i ∈ S
  · simp only [hi, ite_true, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    exact sq_nonneg _
  · simp only [hi, ite_false, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hg.le (abs_nonneg _)).mpr (hgap i hi)) (sq_nonneg _)

/-- The distance to the exact spectral cluster is residual divided by the
separation from every discarded eigenvalue. -/
theorem projection_error_norm (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : ι → ℝ) (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (S : Finset ι) (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - c|) (u : E) :
    ‖u - projection b S u‖ ≤ ‖T u - (c : ℂ) • u‖ / g := by
  have hsq := projection_error_sq b T μ hdiag S c g hg hgap u
  have hmul : g * ‖u - projection b S u‖ ≤ ‖T u - (c : ℂ) • u‖ := by
    apply (sq_le_sq₀ (mul_nonneg hg.le (norm_nonneg _)) (norm_nonneg _)).mp
    simpa only [mul_pow] using hsq
  exact (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using hmul)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Operator-norm form: the whole trial map is controlled by its actual
centered residual, not by a supplied projection-error premise. -/
theorem trialMap_projection_error_opNorm (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (μ : ι → ℝ)
    (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (S : Finset ι) (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - c|) (U : V →L[ℂ] E) :
    ‖U - (projection b S).comp U‖ ≤ ‖T.comp U - (c : ℂ) • U‖ / g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hg.le)
  intro v
  calc
    ‖(U - (projection b S).comp U) v‖ = ‖U v - projection b S (U v)‖ := rfl
    _ ≤ ‖T (U v) - (c : ℂ) • U v‖ / g :=
      projection_error_norm b T.toLinearMap μ hdiag S c g hg hgap (U v)
    _ ≤ (‖T.comp U - (c : ℂ) • U‖ * ‖v‖) / g :=
      div_le_div_of_nonneg_right ((T.comp U - (c : ℂ) • U).le_opNorm v) hg.le
    _ = (‖T.comp U - (c : ℂ) • U‖ / g) * ‖v‖ := by ring

/-- Pointwise residual bounds give the same trial-map estimate. -/
theorem trialMap_projection_error_of_residual (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (μ : ι → ℝ)
    (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (S : Finset ι) (c g ε : ℝ) (hg : 0 < g) (hε : 0 ≤ ε)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - c|) (U : V →L[ℂ] E)
    (hres : ∀ v, ‖T (U v) - (c : ℂ) • U v‖ ≤ ε * ‖v‖) :
    ‖U - (projection b S).comp U‖ ≤ ε / g := by
  apply (trialMap_projection_error_opNorm b T μ hdiag S c g hg hgap U).trans
  exact div_le_div_of_nonneg_right
    ((T.comp U - (c : ℂ) • U).opNorm_le_bound hε hres) hg.le

section VaryingCenters

variable {κ W : Type*} [Fintype κ]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

omit [Fintype ι] [DecidableEq ι] in
/-- A map's operator norm is bounded by its column norm in an orthonormal
basis; this permits different certified centers for different trial columns. -/
theorem opNorm_le_sqrt_sum_basis (a : OrthonormalBasis κ ℂ W) (R : W →L[ℂ] E) :
    ‖R‖ ≤ Real.sqrt (∑ j, ‖R (a j)‖ ^ 2) := by
  apply R.opNorm_le_bound (Real.sqrt_nonneg _)
  intro v
  have hv : R v = ∑ j, a.repr v j • R (a j) := by
    simpa only [map_sum, map_smul] using congrArg R (a.sum_repr v).symm
  calc
    ‖R v‖ ≤ ∑ j, ‖a.repr v j‖ * ‖R (a j)‖ := by
      rw [hv]
      simpa only [norm_smul] using norm_sum_le (Finset.univ) (fun j => a.repr v j • R (a j))
    _ ≤ Real.sqrt (∑ j, ‖a.repr v j‖ ^ 2) * Real.sqrt (∑ j, ‖R (a j)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt (∑ j, ‖R (a j)‖ ^ 2) * ‖v‖ := by
      rw [← norm_sq_eq_sum_repr a, Real.sqrt_sq (norm_nonneg v), mul_comm]

/-- Distinct approximate eigenvalues are allowed for the trial columns.
The resulting operator-norm error is the root sum of squared residual bounds
 divided by the common separation from the discarded spectrum. -/
theorem trialMap_projection_error_varyingCenters (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (μ : ι → ℝ)
    (hdiag : ∀ u i, b.repr (T u) i = (μ i : ℂ) * b.repr u i)
    (S : Finset ι) (g : ℝ) (hg : 0 < g)
    (a : OrthonormalBasis κ ℂ W) (U : W →L[ℂ] E) (c ε : κ → ℝ)
    (hε : ∀ j, 0 ≤ ε j)
    (hgap : ∀ j i, i ∉ S → g ≤ |μ i - c j|)
    (hres : ∀ j, ‖T (U (a j)) - (c j : ℂ) • U (a j)‖ ≤ ε j) :
    ‖U - (projection b S).comp U‖ ≤ Real.sqrt (∑ j, ε j ^ 2) / g := by
  have hc (j : κ) : ‖(U - (projection b S).comp U) (a j)‖ ≤ ε j / g := by
    exact (projection_error_norm b T.toLinearMap μ hdiag S (c j) g hg
      (hgap j) (U (a j))).trans (div_le_div_of_nonneg_right (hres j) hg.le)
  calc
    ‖U - (projection b S).comp U‖ ≤
        Real.sqrt (∑ j, ‖(U - (projection b S).comp U) (a j)‖ ^ 2) :=
      opNorm_le_sqrt_sum_basis a _
    _ ≤ Real.sqrt (∑ j, (ε j / g) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (hε j) hg.le)).mpr (hc j)
    _ = Real.sqrt (∑ j, ε j ^ 2) / g := by
      simp_rw [div_pow]
      rw [← Finset.sum_div, Real.sqrt_div, Real.sqrt_sq hg.le]
      exact Finset.sum_nonneg fun j _ => sq_nonneg (ε j)

end VaryingCenters

section Spectral

variable [FiniteDimensional ℂ E]

/-- Identification with mathlib's canonical orthogonal projector. -/
theorem projection_eq_starProjection_range (b : OrthonormalBasis ι ℂ E) (S : Finset ι) :
    projection b S = (LinearMap.range (projection b S).toLinearMap).starProjection := by
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨u, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact inner_eq_zero_symm.mpr (projection_error_orthogonal b S v u)

/-- Specialization to mathlib's actual Hermitian eigenbasis and eigenvalues. -/
theorem hermitian_projection_error {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (S : Finset (Fin (Module.finrank ℂ E))) (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |hT.eigenvalues rfl i - c|) (u : E) :
    ‖u - projection (hT.eigenvectorBasis rfl) S u‖ ≤ ‖T u - (c : ℂ) • u‖ / g :=
  projection_error_norm (hT.eigenvectorBasis rfl) T (hT.eigenvalues rfl)
    (hT.eigenvectorBasis_apply_self_apply rfl) S c g hg hgap u

/-- Whole-trial-map specialization to the actual Hermitian spectral theorem. -/
theorem hermitian_trialMap_projection_error (T : E →L[ℂ] E)
    (hT : T.toLinearMap.IsSymmetric)
    (S : Finset (Fin (Module.finrank ℂ E))) (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |hT.eigenvalues rfl i - c|) (U : V →L[ℂ] E) :
    ‖U - (projection (hT.eigenvectorBasis rfl) S).comp U‖ ≤
      ‖T.comp U - (c : ℂ) • U‖ / g :=
  trialMap_projection_error_opNorm (hT.eigenvectorBasis rfl) T (hT.eigenvalues rfl)
    (hT.eigenvectorBasis_apply_self_apply rfl) S c g hg hgap U

end Spectral
end
end Maxwell.Spectral.ClusterProjection
