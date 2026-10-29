import Maxwell.Spectral.ClusterProjection
import Mathlib.Tactic

namespace Maxwell.Spectral.ClusterInverse

noncomputable section

open ClusterProjection

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The reduced resolvent vanishes on the selected exact cluster and inverts
the shifted eigenvalues on its orthogonal complement. -/
def reducedInverse (b : OrthonormalBasis ι ℂ H) (μ : ι → ℝ)
    (S : Finset ι) (E : ℝ) : H →L[ℂ] H :=
  ∑ i, (if i ∈ S then 0 else (((μ i - E : ℝ) : ℂ)⁻¹)) •
    InnerProductSpace.rankOne ℂ (b i) (b i)

theorem repr_reducedInverse (b : OrthonormalBasis ι ℂ H) (μ : ι → ℝ)
    (S : Finset ι) (E : ℝ) (v : H) (i : ι) :
    b.repr (reducedInverse b μ S E v) i =
      if i ∈ S then 0 else (((μ i - E : ℝ) : ℂ)⁻¹) * b.repr v i := by
  rw [b.repr_apply_apply]
  simp only [reducedInverse, sum_apply, _root_.smul_apply, InnerProductSpace.rankOne_apply,
    inner_sum, inner_smul_right, b.inner_eq_ite]
  simp [mul_ite, ite_mul, ← b.repr_apply_apply]

theorem projection_reducedInverse (b : OrthonormalBasis ι ℂ H) (μ : ι → ℝ)
    (S : Finset ι) (E : ℝ) :
    (projection b S).comp (reducedInverse b μ S E) = 0 := by
  ext v
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, repr_projection, repr_reducedInverse,
    zero_apply, map_zero, PiLp.zero_apply]
  split_ifs <;> rfl

/-- Multiplying the reduced inverse by the shifted operator yields the exact
complement projection. -/
theorem inverse_equation (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E : ℝ) (hsep : ∀ i, i ∉ S → μ i ≠ E) (v : H) :
    T (reducedInverse b μ S E v) - (E : ℂ) • reducedInverse b μ S E v =
      v - projection b S v := by
  apply b.repr.injective
  ext i
  rw [residual_repr b T μ hdiag, repr_reducedInverse]
  simp only [map_sub, PiLp.sub_apply, repr_projection]
  by_cases hi : i ∈ S
  · simp [hi]
  · have hn : ((μ i - E : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hsep i hi)
    simp only [hi, ite_false, sub_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem complement_projection_norm_le (b : OrthonormalBasis ι ℂ H)
    (S : Finset ι) (v : H) : ‖v - projection b S v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_sum_repr b, norm_sq_eq_sum_repr b]
  apply Finset.sum_le_sum
  intro i _
  simp only [map_sub, PiLp.sub_apply, repr_projection]
  split_ifs <;> simp

theorem reducedInverse_norm_le (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - E|) :
    ‖reducedInverse b μ S E‖ ≤ g⁻¹ := by
  have hsep (i : ι) (hi : i ∉ S) : μ i ≠ E := by
    intro he
    have hh := hgap i hi
    rw [he, sub_self, abs_zero] at hh
    linarith
  apply (reducedInverse b μ S E).opNorm_le_bound (inv_nonneg.mpr hg.le)
  intro v
  have h := projection_error_norm b T μ hdiag S E g hg hgap (reducedInverse b μ S E v)
  have hz : projection b S (reducedInverse b μ S E v) = 0 :=
    congrArg (fun L : H →L[ℂ] H => L v) (projection_reducedInverse b μ S E)
  rw [hz, sub_zero, inverse_equation b T μ hdiag S E hsep] at h
  exact h.trans (by simpa only [div_eq_inv_mul] using
    div_le_div_of_nonneg_right (complement_projection_norm_le b S v) hg.le)

/-- A right-hand side orthogonal to the cluster has an exact corrector,
constructed from the reduced inverse. -/
theorem solve_complement (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E : ℝ) (hsep : ∀ i, i ∉ S → μ i ≠ E)
    (v : H) (hv : projection b S v = 0) :
    T (reducedInverse b μ S E v) - (E : ℂ) • reducedInverse b μ S E v = v := by
  rw [inverse_equation b T μ hdiag S E hsep, hv, sub_zero]

theorem right_inverse_equation (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E : ℝ) (hsep : ∀ i, i ∉ S → μ i ≠ E) (v : H) :
    reducedInverse b μ S E (T v - (E : ℂ) • v) = v - projection b S v := by
  apply b.repr.injective
  ext i
  rw [repr_reducedInverse, residual_repr b T μ hdiag]
  simp only [map_sub, PiLp.sub_apply, repr_projection]
  by_cases hi : i ∈ S
  · simp [hi]
  · have hn : ((μ i - E : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hsep i hi)
    simp only [hi, ite_false, sub_zero]
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- A numerical corrector in the exact cluster complement differs from the
constructed exact corrector by at most its residual divided by the gap. -/
theorem corrector_error (b : OrthonormalBasis ι ℂ H) (T : H →ₗ[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - E|) (rhs y : H)
    (hy : projection b S y = 0) :
    ‖reducedInverse b μ S E rhs - y‖ ≤ ‖rhs - (T y - (E : ℂ) • y)‖ / g := by
  have hsep (i : ι) (hi : i ∉ S) : μ i ≠ E := by
    intro he
    have hh := hgap i hi
    rw [he, sub_self, abs_zero] at hh
    linarith
  have he : reducedInverse b μ S E rhs - y =
      reducedInverse b μ S E (rhs - (T y - (E : ℂ) • y)) := by
    rw [map_sub, right_inverse_equation b T μ hdiag S E hsep, hy, sub_zero]
  rw [he, div_eq_inv_mul]
  exact ((reducedInverse b μ S E).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (reducedInverse_norm_le b T μ hdiag S E g hg hgap)
      (norm_nonneg _))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Operator version of the corrector residual bound, retaining all trial
columns and their Euclidean operator norm. -/
theorem corrector_error_opNorm (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (μ : ι → ℝ) (hdiag : ∀ v i, b.repr (T v) i = (μ i : ℂ) * b.repr v i)
    (S : Finset ι) (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, i ∉ S → g ≤ |μ i - E|) (B Y : V →L[ℂ] H)
    (hY : ∀ x, projection b S (Y x) = 0) :
    ‖(reducedInverse b μ S E).comp B - Y‖ ≤
      ‖B - (T - (E : ℂ) • ContinuousLinearMap.id ℂ H).comp Y‖ / g := by
  apply ((reducedInverse b μ S E).comp B - Y).opNorm_le_bound
    (div_nonneg (norm_nonneg _) hg.le)
  intro x
  have h := corrector_error b T.toLinearMap μ hdiag S E g hg hgap (B x) (Y x) (hY x)
  calc
    _ ≤ ‖B x - (T (Y x) - (E : ℂ) • Y x)‖ / g := h
    _ ≤ (‖B - (T - (E : ℂ) • ContinuousLinearMap.id ℂ H).comp Y‖ * ‖x‖) / g :=
      div_le_div_of_nonneg_right
        ((B - (T - (E : ℂ) • ContinuousLinearMap.id ℂ H).comp Y).le_opNorm x) hg.le
    _ = _ := by ring

end
end Maxwell.Spectral.ClusterInverse
