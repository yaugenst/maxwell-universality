import Maxwell.Green.CauchyRemainder
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Topology.Compactness.Compact

/-! Joint smoothness of parameterized fixed-circle Cauchy remainders. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

universe u

variable {H E : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ H] in
/-- A compact integration domain turns local joint conditions into one
parameter neighborhood on which the conditions hold on the whole domain. -/
theorem eventually_forall_compact_fiber {K : Set ℝ} (hK : IsCompact K)
    {x₀ : H} {P : H × ℝ → Prop}
    (hP : ∀ t ∈ K, ∀ᶠ y in 𝓝 (x₀, t), P y) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, P (x, t) := by
  have h : {y | P y} ∈ (𝓝 x₀) ×ˢ (𝓝ˢ K) :=
    hK.mem_prod_nhdsSet_of_forall (fun t ht => by
      change ∀ᶠ y in (𝓝 x₀) ×ˢ (𝓝 t), P y
      rw [← nhds_prod_eq]
      exact hP t ht)
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  filter_upwards [hU] with x hx
  intro t ht
  exact hUV ⟨hx, subset_of_mem_nhdsSet hV ht⟩

omit [NormedSpace ℝ H] [NormedSpace ℝ E] in
/-- Joint continuity on a compact parameter fiber gives a constant local
dominating function, without assuming any derivative bound. -/
theorem exists_bound_compact_fiber {F : H × ℝ → E} {K : Set ℝ} (hK : IsCompact K)
    {x₀ : H} (hF : ∀ t ∈ K, ContinuousAt F (x₀, t)) :
    ∃ C : ℝ, ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, ‖F (x, t)‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => F (x₀, t)) K := fun t ht =>
    ((hF t ht).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨C + 1, eventually_forall_compact_fiber hK (P := fun y => ‖F y‖ ≤ C + 1) ?_⟩
  intro t ht
  have hlt : ‖F (x₀, t)‖ < C + 1 := (hC _ ⟨t, ht, rfl⟩).trans_lt (by linarith)
  exact ((hF t ht).norm.eventually (gt_mem_nhds hlt)).mono (fun _ h => h.le)

def parameterFDeriv (F : H × ℝ → E) (x : H × ℝ) : H →L[ℝ] E :=
  (fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ H ℝ)

/-- Differentiation of a compact-domain integral follows from joint `C¹`
regularity near its compact fiber. All local domination is derived. -/
theorem hasFDerivAt_setIntegral_compact {F : H × ℝ → E} {K : Set ℝ}
    (hK : IsCompact K) {x₀ : H}
    (hF : ∀ t ∈ K, ContDiffAt ℝ 1 F (x₀, t)) :
    HasFDerivAt (fun x : H => ∫ t in K, F (x, t))
      (∫ t in K, parameterFDeriv F (x₀, t)) x₀ := by
  have hloc : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, ContDiffAt ℝ 1 F (x, t) :=
    eventually_forall_compact_fiber hK (fun t ht => (hF t ht).eventually (by simp))
  have hdc : ∀ t ∈ K, ContinuousAt (parameterFDeriv F) (x₀, t) := by
    intro t ht
    exact (((hF t ht).fderiv_right (m := 0) (by norm_num)).clm_comp
      contDiffAt_const).continuousAt
  obtain ⟨C, hbound⟩ := exists_bound_compact_fiber hK hdc
  let s : Set H := {x | (∀ t ∈ K, ContDiffAt ℝ 1 F (x, t)) ∧
    ∀ t ∈ K, ‖parameterFDeriv F (x, t)‖ ≤ C}
  have hs : s ∈ 𝓝 x₀ := hloc.and hbound
  have hc (x : H) (hx : ∀ t ∈ K, ContDiffAt ℝ 1 F (x, t)) :
      ContinuousOn (fun t : ℝ => F (x, t)) K := fun t ht =>
    ((hx t ht).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x t => parameterFDeriv F (x, t))
    (bound := fun _ => C) hs
  · filter_upwards [hloc] with x hx
    exact (hc x hx).aestronglyMeasurable hK.measurableSet
  · exact (hc x₀ hF).integrableOn_compact hK
  · have hc' : ContinuousOn (fun t : ℝ => parameterFDeriv F (x₀, t)) K := fun t ht =>
      ((hdc t ht).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    exact hc'.aestronglyMeasurable hK.measurableSet
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro x hx
    exact hx.2 t ht
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro x hx
    exact ((hx.1 t ht).differentiableAt_one.hasFDerivAt).comp x
      (hasFDerivAt_prodMk_left x t)

/-- Integration over a compact real domain preserves all finite orders of
joint smoothness. This is proved by induction using the actual parameter
derivative integrals. -/
theorem contDiffAt_setIntegral_compact_nat (F : H × ℝ → E) {K : Set ℝ}
    (hK : IsCompact K) {x₀ : H}
    (hF : ∀ t ∈ K, ContDiffAt ℝ ∞ F (x₀, t)) (n : ℕ) :
    ContDiffAt ℝ n (fun x : H => ∫ t in K, F (x, t)) x₀ := by
  induction n generalizing E with
  | zero =>
    have hloc : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, ContDiffAt ℝ 1 F (x, t) :=
      eventually_forall_compact_fiber hK (fun t ht =>
        ((hF t ht).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp))
    exact contDiffAt_zero.mpr ⟨_, hloc, fun x hx =>
      (hasFDerivAt_setIntegral_compact hK hx).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ t in K, parameterFDeriv F (x, t), ?_, ?_⟩
    · have hloc : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, ContDiffAt ℝ 1 F (x, t) :=
        eventually_forall_compact_fiber hK (fun t ht =>
          ((hF t ht).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp))
      exact ⟨_, hloc, fun x hx => hasFDerivAt_setIntegral_compact hK hx⟩
    · apply ih (parameterFDeriv F)
      intro t ht
      exact ((hF t ht).fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const

theorem contDiffAt_setIntegral_compact (F : H × ℝ → E) {K : Set ℝ}
    (hK : IsCompact K) {x₀ : H}
    (hF : ∀ t ∈ K, ContDiffAt ℝ ∞ F (x₀, t)) :
    ContDiffAt ℝ ∞ (fun x : H => ∫ t in K, F (x, t)) x₀ :=
  contDiffAt_infty.mpr (contDiffAt_setIntegral_compact_nat F hK hF)

section Cauchy

open Complex

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]

def cauchyBoundaryKernel (A B : W × ℂ → ℂ) (R : ℝ) (x : (W × ℂ) × ℝ) : ℂ :=
  deriv (circleMap 0 R) x.2 *
    ((circleMap 0 R x.2 - x.1.2)⁻¹ *
      (A (x.1.1, circleMap 0 R x.2) / B (x.1.1, circleMap 0 R x.2)))

set_option maxHeartbeats 1000000 in
/-- The boundary kernel is jointly real smooth in every parameter because
its two denominators are separated from zero on the fixed outer circle. -/
theorem contDiffAt_cauchyBoundaryKernel (A B : W × ℂ → ℂ)
    (w₀ : W) (u₀ : ℂ) (R θ : ℝ)
    (hA : AnalyticAt ℂ A (w₀, circleMap 0 R θ))
    (hB : AnalyticAt ℂ B (w₀, circleMap 0 R θ))
    (hB₀ : B (w₀, circleMap 0 R θ) ≠ 0) (hu : ‖u₀‖ < R) :
    ContDiffAt ℝ ∞ (cauchyBoundaryKernel A B R) ((w₀, u₀), θ) := by
  have hc : ContDiff ℝ ∞ (fun x : (W × ℂ) × ℝ => circleMap 0 R x.2) :=
    (contDiff_circleMap 0 R).comp contDiff_snd
  have hp : ContDiff ℝ ∞ (fun x : (W × ℂ) × ℝ => (x.1.1, circleMap 0 R x.2)) :=
    contDiff_fst.fst.prodMk hc
  have hAr : ContDiffAt ℝ ∞ A (w₀, circleMap 0 R θ) := hA.restrictScalars.contDiffAt
  have hBr : ContDiffAt ℝ ∞ B (w₀, circleMap 0 R θ) := hB.restrictScalars.contDiffAt
  have hn : circleMap 0 R θ - u₀ ≠ 0 := by
    apply sub_ne_zero.mpr
    exact circleMap_ne_mem_ball (by simpa only [mem_ball, dist_zero_right] using hu) θ
  unfold cauchyBoundaryKernel
  simp only [deriv_circleMap, div_eq_mul_inv]
  exact (hc.contDiffAt.mul contDiffAt_const).mul
    (((hc.contDiffAt.sub contDiffAt_fst.snd).inv hn).mul
      ((hAr.comp ((w₀, u₀), θ) hp.contDiffAt).mul
        ((hBr.comp ((w₀, u₀), θ) hp.contDiffAt).inv hB₀)))

/-- The actual outer-circle Cauchy remainder is jointly `C∞` in transverse
and normal variables on the inner disk. Analyticity is required only near
the fixed outer circle, and all integral differentiation bounds follow
from compactness of that circle. -/
theorem contDiffAt_normalCauchyRemainder (A B : W × ℂ → ℂ)
    (w₀ : W) (u₀ : ℂ) (R : ℝ)
    (hA : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ A (w₀, z))
    (hB : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ B (w₀, z))
    (hB₀ : ∀ z ∈ sphere (0 : ℂ) R, B (w₀, z) ≠ 0) (hu : ‖u₀‖ < R) :
    ContDiffAt ℝ ∞ (fun x : W × ℂ =>
      normalCauchyRemainder (fun z => A (x.1, z)) (fun z => B (x.1, z)) 0 R x.2)
      (w₀, u₀) := by
  have hR : 0 < R := (norm_nonneg u₀).trans_lt hu
  have hkernel : ∀ θ ∈ Icc 0 (2 * Real.pi),
      ContDiffAt ℝ ∞ (cauchyBoundaryKernel A B R) ((w₀, u₀), θ) := by
    intro θ _
    have hz := circleMap_mem_sphere (0 : ℂ) hR.le θ
    exact contDiffAt_cauchyBoundaryKernel A B w₀ u₀ R θ
      (hA _ hz) (hB _ hz) (hB₀ _ hz) hu
  have hi := contDiffAt_setIntegral_compact (cauchyBoundaryKernel A B R)
    isCompact_Icc hkernel
  have he : (fun x : W × ℂ =>
      normalCauchyRemainder (fun z => A (x.1, z)) (fun z => B (x.1, z)) 0 R x.2) =
      fun x : W × ℂ => (2 * Real.pi * I : ℂ)⁻¹ *
        ∫ θ in Icc 0 (2 * Real.pi), cauchyBoundaryKernel A B R (x, θ) := by
    funext x
    rw [normalCauchyRemainder, circleIntegral_def_Icc]
    rfl
  rw [he]
  exact contDiffAt_const.mul hi

/-- The real normal chart used by the Fourier integral is a smooth
restriction of the jointly smooth complex normal chart. -/
theorem contDiffAt_normalCauchyRemainder_real (A B : W × ℂ → ℂ)
    (w₀ : W) (u₀ R : ℝ)
    (hA : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ A (w₀, z))
    (hB : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ B (w₀, z))
    (hB₀ : ∀ z ∈ sphere (0 : ℂ) R, B (w₀, z) ≠ 0) (hu : |u₀| < R) :
    ContDiffAt ℝ ∞ (fun x : W × ℝ =>
      normalCauchyRemainder (fun z => A (x.1, z)) (fun z => B (x.1, z)) 0 R x.2)
      (w₀, u₀) := by
  have huc : ‖(u₀ : ℂ)‖ < R := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
  have h := contDiffAt_normalCauchyRemainder A B w₀ u₀ R hA hB hB₀ huc
  have hc : ContDiffAt ℝ ∞ (fun x : W × ℝ => (x.1, (x.2 : ℂ))) (w₀, u₀) :=
    contDiffAt_fst.prodMk
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (w₀, u₀) contDiffAt_snd)
  simpa only [Function.comp_def] using h.comp (w₀, u₀) hc

end Cauchy

end Maxwell.Green
