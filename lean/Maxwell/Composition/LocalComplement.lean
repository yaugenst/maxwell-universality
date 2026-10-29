import Maxwell.Composition.PhysicalPlatform
import Maxwell.Defect.RobustGap

/-! A simple physical mode determines its actual complementary inverse.
The inverse and a positive rational bound are constructed from simplicity. -/
noncomputable section
namespace Maxwell.Composition
open scoped InnerProduct

theorem exists_local_complement {k : ℕ}
    (G : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (u : EuclideanSpace ℝ (Fin k)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hGu : G u = μ • u)
    (hs : G.toLinearMap.IsSymmetric)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace G.toLinearMap μ) = 1) :
    ∃ (γ : ℚ) (e : LocalModeComplement u ≃L[ℝ] LocalModeComplement u),
      0 < γ ∧
      (∀ x : LocalModeComplement u,
        (e x : EuclideanSpace ℝ (Fin k)) = μ • (x : EuclideanSpace ℝ (Fin k)) - G x) ∧
      ‖(e.symm : LocalModeComplement u →L[ℝ] LocalModeComplement u)‖ ≤ 1 / (γ : ℝ) := by
  obtain ⟨g, hg, hgap⟩ := Maxwell.Defect.simple_eigenpair_has_complementary_gap G u μ hu hGu hsimple
  obtain ⟨γ, hγ, hγg⟩ := exists_rat_btwn hg
  have hγQ : (0 : ℚ) < γ := by exact_mod_cast hγ
  let U := LocalModeComplement u
  let A : U →ₗ[ℝ] U :=
    ((μ • LinearMap.id - G.toLinearMap).domRestrict U).codRestrict U (by
      intro x
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      have hx : inner ℝ u (x : EuclideanSpace ℝ (Fin k)) = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
      change inner ℝ u (μ • (x : EuclideanSpace ℝ (Fin k)) - G x) = 0
      rw [inner_sub_right, inner_smul_right, ← hs.apply_clm, hGu, real_inner_smul_left, hx]
      ring)
  have hA (x : U) : (A x : EuclideanSpace ℝ (Fin k)) =
      μ • (x : EuclideanSpace ℝ (Fin k)) - G x := rfl
  have hbound (x : U) : (γ : ℝ) * ‖x‖ ≤ ‖A x‖ := by
    have hx := hgap x (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
    change (γ : ℝ) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ≤
      ‖μ • (x : EuclideanSpace ℝ (Fin k)) - G x‖
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_right hγg.le (norm_nonneg _)).trans hx
  have hi : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh := hbound x
    rw [hx, norm_zero] at hh
    have hn : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  let e : U ≃L[ℝ] U :=
    (LinearEquiv.ofBijective A ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  refine ⟨γ, e, hγQ, fun x => hA x, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (one_div_pos.mpr hγ).le
  intro x
  have hh := hbound (e.symm x)
  have hcancel : A (e.symm x) = x := e.apply_symm_apply x
  rw [hcancel] at hh
  have hh' : ‖e.symm x‖ ≤ ‖x‖ / (γ : ℝ) :=
    (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hh)
  change ‖e.symm x‖ ≤ 1 / (γ : ℝ) * ‖x‖
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh'

end Maxwell.Composition
