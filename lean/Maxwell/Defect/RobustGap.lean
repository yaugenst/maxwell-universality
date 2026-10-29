import Maxwell.Defect.RankOneResidual

/-! A complementary gap persists under changes of the operator, target,
and selected unit direction. This is the analytic completeness estimate
behind the finite rational eigenpair checker. -/
namespace Maxwell.Defect
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quantitative continuity of the complementary lower bound. -/
theorem complementary_gap_perturbation
    (S A : E →L[ℝ] E) (u v : E) (μ ν γ η ζ δ : ℝ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u) (hγ : 0 ≤ γ)
    (hgap : ∀ y : E, inner ℝ u y = 0 → γ * ‖y‖ ≤ ‖S y - μ • y‖)
    (hoperator : ‖S - A‖ ≤ η) (htarget : |μ - ν| ≤ ζ)
    (hdirection : ‖u - v‖ ≤ δ) :
    ∀ x : E, inner ℝ v x = 0 →
      (γ * (1 - δ) - η - ζ) * ‖x‖ ≤ ‖A x - ν • x‖ := by
  intro x hx
  let a := inner ℝ u x
  let y := x - a • u
  have ha : |a| ≤ δ * ‖x‖ := by
    have heq : a = inner ℝ (u - v) x := by simp [a, inner_sub_left, hx]
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hdirection (norm_nonneg _))
  have hy : inner ℝ u y = 0 := by
    simp [y, a, inner_sub_right, inner_smul_right, hu]
  have hnorm : (1 - δ) * ‖x‖ ≤ ‖y‖ := by
    have hh := norm_add_le y (a • u)
    have hid : y + a • u = x := by dsimp [y]; abel
    rw [hid, norm_smul, Real.norm_eq_abs, hu, mul_one] at hh
    nlinarith
  have hres : S y - μ • y = S x - μ • x := by
    simp only [y, map_sub, map_smul, hSu, smul_sub, smul_smul]
    module
  have hfirst : γ * (1 - δ) * ‖x‖ ≤ ‖S x - μ • x‖ := by
    calc
      _ = γ * ((1 - δ) * ‖x‖) := by ring
      _ ≤ γ * ‖y‖ := mul_le_mul_of_nonneg_left hnorm hγ
      _ ≤ ‖S y - μ • y‖ := hgap y hy
      _ = _ := congrArg norm hres
  have hdiff : ‖(S x - μ • x) - (A x - ν • x)‖ ≤ (η + ζ) * ‖x‖ := by
    have hid : (S x - μ • x) - (A x - ν • x) =
        (S - A) x - (μ - ν) • x := by simp only [sub_apply, sub_smul]; abel
    rw [hid]
    calc
      _ ≤ ‖(S - A) x‖ + ‖(μ - ν) • x‖ := norm_sub_le _ _
      _ ≤ η * ‖x‖ + ζ * ‖x‖ := add_le_add
        (((S - A).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _)))
        (by simpa only [norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_right htarget (norm_nonneg x))
      _ = _ := by ring
  have hh := norm_sub_norm_le (S x - μ • x) (A x - ν • x)
  nlinarith

/-- In finite dimension, simplicity of an actual unit eigenpair supplies
its positive complementary operator gap. It need not be assumed separately. -/
theorem simple_eigenpair_has_complementary_gap [FiniteDimensional ℝ E]
    (S : E →L[ℝ] E) (u : E) (μ : ℝ) (hu : ‖u‖ = 1)
    (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace S.toLinearMap μ) = 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : E, inner ℝ u x = 0 →
      γ * ‖x‖ ≤ ‖S x - μ • x‖ := by
  let U : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let R : U →ₗ[ℝ] E := (S.toLinearMap - μ • LinearMap.id).domRestrict U
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hspan : Module.End.eigenspace S.toLinearMap μ = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple
      (Module.End.mem_eigenspace_iff.mpr hSu) hu0
  have hker : LinearMap.ker R = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have heig : (x : E) ∈ Module.End.eigenspace S.toLinearMap μ := by
      apply Module.End.mem_eigenspace_iff.mpr
      change S (x : E) - μ • (x : E) = 0 at hx
      exact sub_eq_zero.mp hx
    rw [hspan] at heig
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp heig
    have ho : inner ℝ u (x : E) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    rw [← hc] at ho
    have hc0 : c = 0 := by simpa [inner_smul_right, hu] using ho
    apply Subtype.ext
    simpa [hc0] using hc.symm
  obtain ⟨K, hK, hbound⟩ := R.exists_antilipschitzWith hker
  have hKr : 0 < (K : ℝ) := hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKr, ?_⟩
  intro x hx
  let y : U := ⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx⟩
  have hh := ZeroHomClass.bound_of_antilipschitz R hbound y
  change ‖x‖ ≤ (K : ℝ) * ‖S x - μ • x‖ at hh
  exact (inv_mul_le_iff₀ hKr).mpr hh

end Maxwell.Defect
