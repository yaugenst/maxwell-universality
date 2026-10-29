import Maxwell.Green.Implicit
import Maxwell.Green.Taylor
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-! # The quadratic jet of the implicit pole location -/

open Filter
open scoped Topology

namespace Maxwell.Green

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Differentiating the implicit root equation twice at a stationary root
relates its quadratic jet to the purely transverse denominator Hessian. -/
theorem implicit_second_derivative_identity
    {D : W × ℂ → ℂ} {p : W → ℂ}
    (hD : AnalyticAt ℂ D (0, 0)) (hp : AnalyticAt ℂ p 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0) (v : W) :
    (fderiv ℂ D (0, 0)) (0, (fderiv ℂ (fderiv ℂ p) 0) v v) +
      (fderiv ℂ (fderiv ℂ D) (0, 0)) (v, 0) (v, 0) = 0 := by
  let graph : W → W × ℂ := fun w => (w, p w)
  let G : W → ℂ := fun w => (fderiv ℂ D (graph w)) (v, (fderiv ℂ p w) v)
  have hgraph : AnalyticAt ℂ graph 0 := analyticAt_id.prod hp
  have hgraph₀ : graph 0 = (0, 0) := by simp [graph, hp₀]
  have hgraph' : HasFDerivAt graph (ContinuousLinearMap.inl ℂ W ℂ) 0 := by
    have hid : (ContinuousLinearMap.id ℂ W).prod (0 : W →L[ℂ] ℂ) =
        ContinuousLinearMap.inl ℂ W ℂ := by ext w <;> rfl
    simpa [graph, hp₁, hid] using
      (hasFDerivAt_id (0 : W)).prodMk hp.differentiableAt.hasFDerivAt
  have hDnear : ∀ᶠ w in 𝓝 (0 : W), AnalyticAt ℂ D (graph w) :=
    hgraph.continuousAt.tendsto.eventually (hgraph₀ ▸ hD.eventually_analyticAt)
  have hzero : (fun w => D (graph w)) =ᶠ[𝓝 (0 : W)] fun _ => (0 : ℂ) := hroot
  have hGzero : G =ᶠ[𝓝 (0 : W)] fun _ => (0 : ℂ) := by
    filter_upwards [hzero.fderiv (𝕜 := ℂ), hDnear, hp.eventually_analyticAt] with w hw hDw hpw
    have hc := hDw.differentiableAt.hasFDerivAt.comp w
      ((hasFDerivAt_id w).prodMk hpw.differentiableAt.hasFDerivAt)
    have heq := hc.fderiv.symm.trans hw
    have hv := congrArg (fun L : W →L[ℂ] ℂ => L v) heq
    simpa [G, graph, Function.comp_def] using hv
  have hA : HasFDerivAt (fun w => fderiv ℂ D (graph w))
      ((fderiv ℂ (fderiv ℂ D) (0, 0)).comp (ContinuousLinearMap.inl ℂ W ℂ)) 0 := by
    have hd := hD.fderiv.differentiableAt.hasFDerivAt
    rw [← hgraph₀] at hd
    simpa only [hgraph₀, Function.comp_def] using hd.comp 0 hgraph'
  have hB := (hasFDerivAt_const v (0 : W)).prodMk
    (hp.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const v (0 : W)))
  have hG := hA.clm_apply hB
  have hderivzero : fderiv ℂ G 0 = 0 := by
    rw [hGzero.fderiv_eq]
    simp
  have heq := hG.fderiv.symm.trans hderivzero
  have hv := congrArg (fun L : W →L[ℂ] ℂ => L v) heq
  simpa [graph, hp₀, hp₁, ContinuousLinearMap.comp_apply] using hv

/-- Solving the differentiated implicit equation gives the exact normal
inverse times transverse Hessian, including its sign. -/
theorem implicit_second_derivative
    {D : W × ℂ → ℂ} {p : W → ℂ}
    (hD : AnalyticAt ℂ D (0, 0)) (hp : AnalyticAt ℂ p 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) (v : W) :
    (fderiv ℂ (fderiv ℂ p) 0) v v =
      -((fderiv ℂ D (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ D) (0, 0)) (v, 0) (v, 0) := by
  have h := implicit_second_derivative_identity hD hp hp₀ hp₁ hroot v
  have hnormal (z : ℂ) : (fderiv ℂ D (0, 0)) (0, z) =
      (fderiv ℂ D (0, 0)) (0, 1) * z :=
    complex_linearMap_apply ((fderiv ℂ D (0, 0)).comp (ContinuousLinearMap.inr ℂ W ℂ)) z
  rw [hnormal] at h
  field_simp
  linear_combination h

/-- The quadratic power-series coefficient is one half of the repeated
Fréchet derivative. The identity holds in arbitrary complex parameter spaces. -/
theorem second_derivative_eq_twice_quadratic
    {p : W → ℂ} {s : FormalMultilinearSeries ℂ W ℂ}
    (hs : HasFPowerSeriesAt p s 0) (v : W) :
    (fderiv ℂ (fderiv ℂ p) 0) v v = 2 * s 2 (fun _ => v) := by
  obtain ⟨r, hr⟩ := hs
  rw [hr.fderiv.hasFPowerSeriesAt.fderiv_eq]
  have hfin : Fin.snoc (0 : Fin 0 → W) v = fun _ : Fin 1 => v := by
    ext i
    fin_cases i
    rfl
  simpa only [continuousMultilinearCurryFin1_apply, hfin, Nat.reduceAdd,
    Nat.cast_ofNat, nsmul_eq_mul] using s.derivSeries_apply_diag 1 v

/-- The quadratic term of the implicit pole is fixed by the denominator
derivatives; it is not an additional asymptotic hypothesis. -/
theorem implicit_quadratic_coefficient
    {D : W × ℂ → ℂ} {p : W → ℂ} {s : FormalMultilinearSeries ℂ W ℂ}
    (hD : AnalyticAt ℂ D (0, 0)) (hs : HasFPowerSeriesAt p s 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) (v : W) :
    s 2 (fun _ => v) = -(2 : ℂ)⁻¹ * ((fderiv ℂ D (0, 0)) (0, 1))⁻¹ *
      (fderiv ℂ (fderiv ℂ D) (0, 0)) (v, 0) (v, 0) := by
  have h := implicit_second_derivative hD hs.analyticAt hp₀ hp₁ hroot hu v
  rw [second_derivative_eq_twice_quadratic hs v] at h
  linear_combination h / 2

/-- Analytic implicit division supplies the cubic phase remainder from local
denominator derivatives and stationarity. -/
theorem implicit_phase_cubic_remainder
    {D : W × ℂ → ℂ} {p : W → ℂ}
    (hD : AnalyticAt ℂ D (0, 0)) (hp : AnalyticAt ℂ p 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) :
    ∃ K > 0, ∃ δ > 0, ∀ w, ‖w‖ < δ →
      ‖p w - (-(2 : ℂ)⁻¹ * ((fderiv ℂ D (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ D) (0, 0)) (w, 0) (w, 0))‖ ≤ K * ‖w‖ ^ 3 := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨K, hK, δ, hδ, hbound⟩ := analytic_quadratic_remainder hs hp₀ hp₁
  refine ⟨K, hK, δ, hδ, fun w hw => ?_⟩
  simpa only [implicit_quadratic_coefficient hD hs hp₀ hp₁ hroot hu w] using hbound w hw

/-- An analytic denominator with a stationary transverse derivative has an
actual analytic pole graph with the exact Hessian-controlled cubic expansion. -/
theorem exists_analytic_stationary_pole [CompleteSpace W]
    (D : W × ℂ → ℂ) (hD : AnalyticAt ℂ D (0, 0)) (hzero : D (0, 0) = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0)
    (htrans : (fderiv ℂ D (0, 0)).comp (ContinuousLinearMap.inl ℂ W ℂ) = 0) :
    ∃ p : W → ℂ, p 0 = 0 ∧ AnalyticAt ℂ p 0 ∧ fderiv ℂ p 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), D z = 0 ↔ p z.1 = z.2) ∧
      ∃ K > 0, ∃ δ > 0, ∀ w, ‖w‖ < δ →
        ‖p w - (-(2 : ℂ)⁻¹ * ((fderiv ℂ D (0, 0)) (0, 1))⁻¹ *
          (fderiv ℂ (fderiv ℂ D) (0, 0)) (w, 0) (w, 0))‖ ≤ K * ‖w‖ ^ 3 := by
  obtain ⟨p, hp₀, hp, hroot, huniq, hp'⟩ := exists_analytic_implicit_root D hD hzero hu
  have hp₁ : fderiv ℂ p 0 = 0 := by
    rw [hp'.hasFDerivAt.fderiv, htrans]
    ext w
    simp only [smul_apply, zero_apply, smul_zero]
  exact ⟨p, hp₀, hp, hp₁, hroot, huniq,
    implicit_phase_cubic_remainder hD hp hp₀ hp₁ hroot hu⟩

/-- When the normal derivative is positive imaginary and the transverse
Hessian is real, the implicit quadratic coefficient has the required positive
imaginary sign. -/
theorem imaginary_normal_quadratic_coefficient {c q : ℝ} (hc : c ≠ 0) :
    -(2 : ℂ)⁻¹ * (Complex.I * (c : ℂ))⁻¹ * (q : ℂ) =
      Complex.I * ((q / (2 * c) : ℝ) : ℂ) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  push_cast
  field_simp
  simp only [Complex.I_sq]
  ring

end Maxwell.Green
