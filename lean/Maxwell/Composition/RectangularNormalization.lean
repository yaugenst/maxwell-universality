import Maxwell.Composition.RectangularMatrix

/-! The standard full-column-rank condition number and cancellation-safe
normalization used in the real-input reduction. -/
noncomputable section
namespace Maxwell.Composition.RectangularSaddle
open scoped InnerProduct
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]
set_option maxHeartbeats 800000

def pseudoInverse (F : E →L[ℝ] H) (hF : Function.Injective F) : H →L[ℝ] E :=
  ((gramEquiv F hF).symm : E →L[ℝ] E).comp F.adjoint

@[simp] theorem pseudoInverse_apply_map (F : E →L[ℝ] H) (hF : Function.Injective F) (x : E) :
    pseudoInverse F hF (F x) = x := (gramEquiv F hF).symm_apply_apply x

/-- The Euclidean condition number of a full-column-rank rectangular map. -/
def condition₂ (F : E →L[ℝ] H) (hF : Function.Injective F) : ℝ :=
  ‖F‖ * ‖pseudoInverse F hF‖

theorem normalized_lower_bound (F₀ F : E →L[ℝ] H) (hF₀ : Function.Injective F₀)
    (m lam : ℝ) (hlam : 0 ≤ lam) (hscale : F₀ = lam • F)
    (hlamnorm : lam ≤ m*‖F₀‖) (x : E) :
    ‖x‖ ≤ (m*condition₂ F₀ hF₀)*‖F x‖ := by
  have hh := (pseudoInverse F₀ hF₀).le_opNorm (F₀ x)
  have hx : ‖F₀ x‖ = lam*‖F x‖ := by
    rw [hscale, smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  rw [pseudoInverse_apply_map, hx] at hh
  have hs := mul_le_mul_of_nonneg_right hlamnorm
    (mul_nonneg (norm_nonneg (pseudoInverse F₀ hF₀)) (norm_nonneg (F x)))
  unfold condition₂
  nlinarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ H] in
theorem normalized_injective (F₀ F : E →L[ℝ] H) (hF₀ : Function.Injective F₀)
    (lam : ℝ) (hscale : F₀ = lam • F) : Function.Injective F := by
  intro x y hxy
  apply hF₀
  rw [hscale, smul_apply, smul_apply, hxy]

theorem projection_zero_of_adjoint (F : E →L[ℝ] H) (hF : Function.Injective F)
    (b : H) (hb : F.adjoint b = 0) : projection F hF b = 0 := by
  simp [projection, hb]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ H] in
theorem scaled_ranges (F₀ F : E →L[ℝ] H) (lam : ℝ) (hlam : lam ≠ 0)
    (hscale : F₀ = lam • F) : F₀.range = F.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨lam • x, ?_⟩
    change F (lam • x) = F₀ x
    rw [map_smul, hscale, smul_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨lam⁻¹ • x, ?_⟩
    change F₀ (lam⁻¹ • x) = F x
    rw [hscale, smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hlam, one_smul]

theorem scaled_projection (F₀ F : E →L[ℝ] H)
    (hF₀ : Function.Injective F₀) (hF : Function.Injective F)
    (lam : ℝ) (hlam : lam ≠ 0) (hscale : F₀ = lam • F) :
    projection F₀ hF₀ = projection F hF := by
  rw [projection_eq_orthogonal, projection_eq_orthogonal]
  exact congrArg (fun U : Submodule ℝ H => U.starProjection) (scaled_ranges F₀ F lam hlam hscale)

theorem projection_from_normalized_source (F : E →L[ℝ] H) (hF : Function.Injective F)
    (b : H) (q zstar : E) (ν : ℝ)
    (hsource : F.adjoint b = ν • q) (hstar : gram F zstar = q) :
    projection F hF b = ν • F zstar := by
  change F ((gramEquiv F hF).symm (F.adjoint b)) = _
  rw [hsource, map_smul, map_smul, ← hstar]
  change ν • F ((gramEquiv F hF).symm (gramEquiv F hF zstar)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem rescaled_projection_relative (F₀ F : E →L[ℝ] H)
    (hF₀ : Function.Injective F₀) (hF : Function.Injective F)
    (lam ν ε : ℝ) (hlam : 0 < lam) (hν : 0 ≤ ν)
    (hscale : F₀ = lam • F) (b : H) (q z zstar : E)
    (hsource : F.adjoint b = ν • q) (hstar : gram F zstar = q)
    (herror : ‖F (z-zstar)‖ ≤ ε*‖F zstar‖) :
    ‖F₀ ((ν/lam) • z) - projection F₀ hF₀ b‖ ≤ ε*‖projection F₀ hF₀ b‖ := by
  have hp : projection F₀ hF₀ b = ν • F zstar := by
    rw [scaled_projection F₀ F hF₀ hF lam hlam.ne' hscale]
    exact projection_from_normalized_source F hF b q zstar ν hsource hstar
  have hv : F₀ ((ν/lam) • z) = ν • F z := by
    rw [hscale, smul_apply, map_smul, smul_smul]
    congr 1
    field_simp
  rw [hp, hv, ← smul_sub, ← map_sub, norm_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hν]
  have hh := mul_le_mul_of_nonneg_left herror hν
  nlinarith

section MatrixBounds
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangular_entry_le_norm (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |A i j| ≤ ‖rectangularEuclideanCLM A‖ := by
  let x : EuclideanSpace ℝ κ := PiLp.single 2 j 1
  have hx : ‖x‖ = 1 := by simp [x]
  have he : rectangularEuclideanCLM A x i = A i j := by
    simp [rectangularEuclideanCLM_apply, x, PiLp.single_apply]
  have hh := (PiLp.norm_apply_le (rectangularEuclideanCLM A x) i).trans
    ((rectangularEuclideanCLM A).le_opNorm x)
  simpa only [he, hx, mul_one, Real.norm_eq_abs] using hh

theorem rectangular_norm_le_total_abs (A : Matrix ι κ ℝ) :
    ‖rectangularEuclideanCLM A‖ ≤ ∑ i, ∑ j, |A i j| := by
  apply rectangularEuclideanCLM_norm_le A _ (by positivity)
  · intro i
    exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (A a b))) (Finset.mem_univ i)
  · intro j
    rw [Finset.sum_comm]
    exact Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun a _ => abs_nonneg (A a b))) (Finset.mem_univ j)

end MatrixBounds
end Maxwell.Composition.RectangularSaddle
