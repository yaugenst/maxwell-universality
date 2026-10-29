import Maxwell.Defect.RankOneTransport

/-! A finite residual and complementary quadratic form certify an actual
simple eigenpair. This supplies a rational-checker route to branch isolation. -/
namespace Maxwell.Defect

open InnerProductSpace Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Replace the one selected row and column by an exact eigenpair, retaining
all of the compressed complementary operator. -/
noncomputable def residualReference (T : E →L[ℝ] E) (u : E) (μ : ℝ) : E →L[ℝ] E :=
  (1 - rankOne ℝ u u) * T * (1 - rankOne ℝ u u) + μ • rankOne ℝ u u

/-- The residual reference has the proposed eigenpair exactly. -/
theorem residualReference_selected (T : E →L[ℝ] E) (u : E) (μ : ℝ) (hu : ‖u‖ = 1) :
    residualReference T u μ u = μ • u := by
  simp [residualReference, mul_apply_eq_comp, rankOne_apply, hu]

/-- Removing the component along a unit vector cannot increase a norm. -/
theorem norm_remove_unit_component_le (u r : E) (hu : ‖u‖ = 1) :
    ‖r - (inner ℝ u r) • u‖ ≤ ‖r‖ := by
  have hh := norm_sub_sq_real r ((inner ℝ u r) • u)
  simp only [inner_smul_right, real_inner_comm u r, norm_smul, Real.norm_eq_abs,
    hu, mul_one, sq_abs] at hh
  nlinarith [sq_nonneg (inner ℝ u r), norm_nonneg r,
    norm_nonneg (r - (inner ℝ u r) • u)]

/-- Exact two-rank-one representation of the alteration made by the
reference construction. -/
theorem residualReference_difference (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    (u : E) (μ : ℝ) (hu : ‖u‖ = 1) :
    let r := T u - μ • u
    T - residualReference T u μ =
      rankOne ℝ u r + rankOne ℝ (r - (inner ℝ u r) • u) u := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro x
  have hsym : inner ℝ u (T x) = inner ℝ (T u) x := (hT u x).symm
  simp only [residualReference, sub_apply, add_apply, mul_apply_eq_comp, one_apply_eq_self,
    rankOne_apply, smul_apply, map_sub, map_smul, inner_sub_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hu, hsym]
  module

/-- The reference differs from the input by at most twice the proposed
unit eigenpair's residual. -/
theorem residualReference_norm (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    (u : E) (μ : ℝ) (hu : ‖u‖ = 1) :
    ‖T - residualReference T u μ‖ ≤ 2 * ‖T u - μ • u‖ := by
  rw [residualReference_difference T hT u μ hu]
  calc
    _ ≤ ‖rankOne ℝ u (T u - μ • u)‖ +
        ‖rankOne ℝ ((T u - μ • u) - (inner ℝ u (T u - μ • u)) • u) u‖ := norm_add_le _ _
    _ = ‖T u - μ • u‖ + ‖(T u - μ • u) - (inner ℝ u (T u - μ • u)) • u‖ := by
      rw [norm_rankOne, norm_rankOne, hu, one_mul, mul_one]
    _ ≤ ‖T u - μ • u‖ + ‖T u - μ • u‖ :=
      add_le_add (le_refl _) (norm_remove_unit_component_le u (T u - μ • u) hu)
    _ = _ := by ring

/-- A global quadratic form inequality is sufficient to certify the
complementary norm gap; it does not postulate an eigenvalue or a branch. -/
theorem complementary_gap_of_quadratic_certificate
    (A : E →L[ℝ] E) (u : E) (μ g : ℝ)
    (hcert : ∀ x : E, g ^ 2 * ‖x‖ ^ 2 ≤
      ‖A x - μ • x‖ ^ 2 + 2 * g ^ 2 * |inner ℝ u x| ^ 2) :
    ∀ x : E, inner ℝ u x = 0 → g * ‖x‖ ≤ ‖A x - μ • x‖ := by
  intro x hx
  have hh := hcert x
  rw [hx, abs_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hh
  nlinarith [norm_nonneg (A x - μ • x)]

/-- An exact unit eigenpair and its complementary norm gap imply the global
quadratic certificate for every smaller nonnegative gap. -/
theorem quadratic_certificate_of_complementary_gap
    (A : E →L[ℝ] E) (u : E) (μ g γ : ℝ) (hu : ‖u‖ = 1)
    (heig : A u = μ • u) (hg : 0 ≤ g) (hgγ : g ≤ γ)
    (hgap : ∀ x : E, inner ℝ u x = 0 → γ * ‖x‖ ≤ ‖A x - μ • x‖) :
    ∀ x : E, g ^ 2 * ‖x‖ ^ 2 ≤
      ‖A x - μ • x‖ ^ 2 + 2 * g ^ 2 * |inner ℝ u x| ^ 2 := by
  intro x
  let a := inner ℝ u x
  let y := x - a • u
  have hy : inner ℝ u y = 0 := by
    simp [y, a, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  have hr : A y - μ • y = A x - μ • x := by
    simp only [y, map_sub, map_smul, heig]
    module
  have hn : ‖y‖ ^ 2 = ‖x‖ ^ 2 - a ^ 2 := by
    have h := norm_sub_sq_real x (a • u)
    simp only [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
      inner_smul_right, real_inner_comm u x] at h
    change ‖x - a • u‖ ^ 2 = ‖x‖ ^ 2 - a ^ 2
    change ‖x - a • u‖ ^ 2 = ‖x‖ ^ 2 - 2 * (a * a) + a ^ 2 at h
    nlinarith
  have hbound : g * ‖y‖ ≤ ‖A x - μ • x‖ := by
    exact (mul_le_mul_of_nonneg_right hgγ (norm_nonneg y)).trans (hr ▸ hgap y hy)
  have hs : (g * ‖y‖) ^ 2 ≤ ‖A x - μ • x‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hg (norm_nonneg y)) hbound 2
  rw [mul_pow, hn] at hs
  rw [sq_abs]
  change g ^ 2 * ‖x‖ ^ 2 ≤ ‖A x - μ • x‖ ^ 2 + 2 * g ^ 2 * a ^ 2
  nlinarith [mul_nonneg (sq_nonneg g) (sq_nonneg a)]

/-- Soundness of the finite residual-and-quadratic-gap certificate. The
certified matrix has an actual simple eigenpair with explicit errors and
separation; no spectral root counting is needed. -/
theorem residual_quadratic_certificate_sound [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (u : E) (μ ε g : ℝ)
    (hu : ‖u‖ = 1) (hres : ‖T u - μ • u‖ ≤ ε)
    (hcert : ∀ x : E, g ^ 2 * ‖x‖ ^ 2 ≤
      ‖residualReference T u μ x - μ • x‖ ^ 2 + 2 * g ^ 2 * |inner ℝ u x| ^ 2)
    (hsmall : 4 * ε < g) :
    ∃ ν : ℝ, ∃ v : E, ‖v‖ = 1 ∧ T v = ν • v ∧ |ν - μ| ≤ 2 * ε ∧
      Module.finrank ℝ (eigenspace T.toLinearMap ν) = 1 ∧ 0 < inner ℝ u v ∧
      ‖v - u‖ ≤ 8 * ε / g ∧
      ∀ (ρ : ℝ) (x : E), ‖x‖ = 1 → T x = ρ • x → ν ≠ ρ →
        g - 4 * ε ≤ |ρ - ν| := by
  let A := residualReference T u μ
  have hbound : ‖T - A‖ ≤ 2 * ε :=
    (residualReference_norm T hT u μ hu).trans (by gcongr)
  have hpert : ∀ x : E, ‖T x - A x‖ ≤ (2 * ε) * ‖x‖ := by
    intro x
    exact ((T - A).le_opNorm x).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  have hgap := complementary_gap_of_quadratic_certificate A u μ g hcert
  obtain ⟨ν, v, hv, hTv, hν, hdim, hinner, halign, hsep⟩ :=
    isolated_eigenpair_stability A.toLinearMap T.toLinearMap hT u μ (2 * ε) g hu
      (residualReference_selected T u μ hu) hgap hpert (by nlinarith)
  refine ⟨ν, v, hv, hTv, hν, hdim, hinner, ?_, ?_⟩
  · simpa only [show 4 * (2 * ε) = 8 * ε by ring] using halign
  · intro ρ x hx hTx hne
    simpa only [show 2 * (2 * ε) = 4 * ε by ring] using hsep ρ x hx hTx hne

end Maxwell.Defect
