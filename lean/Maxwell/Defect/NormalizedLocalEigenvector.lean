import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A local unit eigenvector constructed by normalizing the image of the
actual analytic spectral projector, with a quantitative variation bound. -/

namespace Maxwell.Defect

open Filter Metric Set NormedSpace InnerProductSpace
open scoped Topology ContDiff

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalizing a nonzero vector costs at most twice its distance to a
fixed unit vector. No lower norm bound enters this estimate. -/
theorem normalize_sub_unit_le (x u : E) (hx : x ≠ 0) (hu : ‖u‖ = 1) :
    ‖normalize x - u‖ ≤ 2 * ‖x - u‖ := by
  have hunit : ‖normalize x‖ = 1 := norm_normalize hx
  have hd : ‖normalize x - x‖ ≤ ‖x - u‖ := by
    calc
      _ = ‖(1 - ‖x‖) • normalize x‖ := by
        rw [sub_smul, one_smul, norm_smul_normalize]
      _ = |1 - ‖x‖| := by rw [norm_smul, hunit, mul_one, Real.norm_eq_abs]
      _ ≤ ‖x - u‖ := by simpa only [hu, abs_sub_comm] using abs_norm_sub_norm_le x u
  calc
    _ ≤ ‖normalize x - x‖ + ‖x - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x - u‖ := by linarith

end Normalization

section LocalBranch

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def normalizedProjectorVector (P : X → E →L[ℂ] E) (u : E) (q : X) : E :=
  normalize (P q u)

omit [NormedSpace ℝ X] [CompleteSpace E] in
theorem normalizedProjectorVector_zero (P : X → E →L[ℂ] E) (u : E)
    (hu : ‖u‖ = 1) (hcenter : P 0 u = u) :
    normalizedProjectorVector P u 0 = u := by
  simp only [normalizedProjectorVector, hcenter, normalize_eq_self_of_norm_eq_one hu]

/-- Analyticity of the actual projector supplies a locally continuous
unit eigenvector and a linear variation estimate around its fixed center. -/
theorem exists_normalized_local_eigenvector
    (A P : X → E →L[ℂ] E) (value : X → ℂ) (u : E)
    (hP : AnalyticAt ℝ P 0) (hu : ‖u‖ = 1) (hcenter : P 0 u = u)
    (heigen : ∀ᶠ q in 𝓝 (0 : X), A q (P q u) = value q • P q u) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      normalizedProjectorVector P u 0 = u ∧
      ContinuousOn (normalizedProjectorVector P u) (ball 0 r) ∧
      ∀ q ∈ ball 0 r,
        ‖normalizedProjectorVector P u q‖ = 1 ∧
        A q (normalizedProjectorVector P u q) = value q • normalizedProjectorVector P u q ∧
        ‖normalizedProjectorVector P u q - u‖ ≤ C * ‖q‖ := by
  obtain ⟨L, U, hU, hLip⟩ :=
    ((hP.contDiffAt : ContDiffAt ℝ ∞ P 0).hasStrictFDerivAt (by simp)).exists_lipschitzOnWith
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU heigen)
  let r : ℝ := min r₀ (1 / (2 * ((L : ℝ) + 1)))
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hsub : ball (0 : X) r ⊆ U := by
    intro q hq
    exact (hball (ball_subset_ball (min_le_left _ _) hq)).1
  have hvariation (q : X) (hq : q ∈ ball 0 r) : ‖P q u - u‖ ≤ (L : ℝ) * ‖q‖ := by
    calc
      _ = ‖(P q - P 0) u‖ := by rw [sub_apply, hcenter]
      _ ≤ ‖P q - P 0‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((L : ℝ) * ‖q‖) * ‖u‖ := mul_le_mul_of_nonneg_right
        (by simpa only [sub_zero] using hLip.norm_sub_le (hsub hq) (mem_of_mem_nhds hU))
        (norm_nonneg _)
      _ = _ := by rw [hu, mul_one]
  have hnonzero (q : X) (hq : q ∈ ball 0 r) : P q u ≠ 0 := by
    have hqnorm : ‖q‖ < 1 / (2 * ((L : ℝ) + 1)) :=
      (mem_ball_zero_iff.mp hq).trans_le (min_le_right _ _)
    have hsmall : (L : ℝ) * ‖q‖ < 1 := by
      have hh := (lt_div_iff₀ (show (0 : ℝ) < 2 * ((L : ℝ) + 1) by positivity)).mp hqnorm
      nlinarith [norm_nonneg q, L.coe_nonneg]
    intro hz
    have hv := hvariation q hq
    simp only [hz, zero_sub, norm_neg, hu] at hv
    linarith
  have hvcont : ContinuousOn (fun q => P q u) (ball (0 : X) r) :=
    (hLip.continuousOn.mono hsub).clm_apply continuousOn_const
  have hncont : ContinuousOn (normalizedProjectorVector P u) (ball (0 : X) r) :=
    (hvcont.norm.inv₀ (fun q hq => norm_ne_zero_iff.mpr (hnonzero q hq))).smul hvcont
  refine ⟨r, 2 * ((L : ℝ) + 1), hr, by positivity,
    normalizedProjectorVector_zero P u hu hcenter, hncont, ?_⟩
  intro q hq
  refine ⟨norm_normalize (hnonzero q hq), ?_, ?_⟩
  · have heq := (hball (ball_subset_ball (min_le_left _ _) hq)).2
    dsimp only [normalizedProjectorVector, NormedSpace.normalize]
    rw [ContinuousLinearMap.map_smul_of_tower, heq, smul_comm]
  · calc
      _ ≤ 2 * ‖P q u - u‖ := normalize_sub_unit_le _ _ (hnonzero q hq) hu
      _ ≤ 2 * ((L : ℝ) * ‖q‖) := mul_le_mul_of_nonneg_left (hvariation q hq) (by norm_num)
      _ ≤ (2 * ((L : ℝ) + 1)) * ‖q‖ := by nlinarith [norm_nonneg q]

end LocalBranch

section Projector

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Operator-valued spectral projector identities provide all the inputs
to the normalized branch construction. -/
theorem exists_normalized_local_eigenvector_of_projector
    (A P : X → E →L[ℂ] E) (value : X → ℂ) (u : E)
    (hP : AnalyticAt ℝ P 0) (hu : ‖u‖ = 1)
    (hcenter : P 0 = rankOne ℂ u u)
    (heigen : ∀ᶠ q in 𝓝 (0 : X), A q * P q = value q • P q) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      normalizedProjectorVector P u 0 = u ∧
      ContinuousOn (normalizedProjectorVector P u) (ball 0 r) ∧
      ∀ q ∈ ball 0 r,
        ‖normalizedProjectorVector P u q‖ = 1 ∧
        A q (normalizedProjectorVector P u q) = value q • normalizedProjectorVector P u q ∧
        ‖normalizedProjectorVector P u q - u‖ ≤ C * ‖q‖ := by
  apply exists_normalized_local_eigenvector A P value u hP hu
  · simp [hcenter, rankOne_apply, inner_self_eq_norm_sq_to_K, hu]
  · filter_upwards [heigen] with q hq
    exact congrArg (fun T : E →L[ℂ] E => T u) hq

end Projector

end Maxwell.Defect
