import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Maxwell.Green.Taylor

/-! # Analytic simple-pole division and the exact Fourier residue -/

open Filter Metric Complex
open scoped Topology

namespace Maxwell.Green

/-- Removing a first-order difference preserves analyticity at its center. -/
theorem analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s.fslope, hs.has_fpower_series_dslope_fslope⟩

/-- Exact analytic division at a simple spectral pole. The denominator
factor and the regular remainder are constructed by divided differences;
the residue is `A(p)/D'(p)`. -/
theorem simple_pole_division {A D : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hD : AnalyticAt ℂ D p)
    (hDp : D p = 0) (hD' : deriv D p ≠ 0) :
    ∃ d g : ℂ → ℂ,
      AnalyticAt ℂ d p ∧ AnalyticAt ℂ g p ∧ d p = deriv D p ∧
      (∀ z, D z = (z - p) * d z) ∧
      (∀ᶠ z in 𝓝 p, d z ≠ 0 ∧
        (z ≠ p → A z / D z = (A p / deriv D p) / (z - p) + g z)) := by
  let d := dslope D p
  let B : ℂ → ℂ := fun z => A z / d z
  let g := dslope B p
  have hd : AnalyticAt ℂ d p := analyticAt_dslope hD
  have hdp : d p = deriv D p := dslope_same D p
  have hdp0 : d p ≠ 0 := by rwa [hdp]
  have hB : AnalyticAt ℂ B p := hA.div hd hdp0
  have hg : AnalyticAt ℂ g p := analyticAt_dslope hB
  have hfactor : ∀ z, D z = (z - p) * d z := by
    intro z
    simpa only [hDp, sub_zero, smul_eq_mul] using (sub_smul_dslope D p z).symm
  refine ⟨d, g, hd, hg, hdp, hfactor, ?_⟩
  filter_upwards [hd.continuousAt.eventually_ne hdp0] with z hdz
  refine ⟨hdz, fun hzp => ?_⟩
  have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hgEq : B z = (z - p) * g z + B p := by
    have h := sub_smul_dslope B p z
    simp only [smul_eq_mul] at h
    change (z - p) * g z = B z - B p at h
    exact (sub_eq_iff_eq_add.mp h.symm)
  calc
    A z / D z = B z / (z - p) := by
      rw [hfactor z]
      dsimp [B]
      field_simp
    _ = B p / (z - p) + g z := by
      rw [hgEq]
      field_simp
      ring
    _ = (A p / deriv D p) / (z - p) + g z := by
      dsimp [B]
      rw [hdp]

/-- The residue of a Fourier factor at a pole in a disk. This is the exact
closed-contour identity used before bounding the non-real contour pieces. -/
theorem fourier_pole_circleIntegral {p center : ℂ} {R : ℝ}
    (hp : p ∈ ball center R) (T : ℝ) :
    (∮ z in C(center, R), Complex.exp (Complex.I * T * z) / (z - p)) =
      (2 * (Real.pi : ℂ) * Complex.I) * Complex.exp (Complex.I * T * p) := by
  have hdiff : Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * T * z)) := by
    fun_prop
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hdiff.differentiableOn.circleIntegral_sub_inv_smul hp

/-- The moving-pole residue is an actual analytic function of the transverse
parameters. Its denominator is the normal derivative on the root graph. -/
theorem analytic_residue_amplitude
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {A D : W × ℂ → ℂ} {p : W → ℂ}
    (hA : AnalyticAt ℂ A (0, 0)) (hD : AnalyticAt ℂ D (0, 0))
    (hp : AnalyticAt ℂ p 0) (hp₀ : p 0 = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) :
    AnalyticAt ℂ (fun w => A (w, p w) / (fderiv ℂ D (w, p w)) (0, 1)) 0 := by
  have hgraph : AnalyticAt ℂ (fun w => (w, p w)) 0 := analyticAt_id.prod hp
  have hgraph₀ : ((0 : W), p 0) = (0, 0) := by rw [hp₀]
  exact (hA.comp_of_eq hgraph hgraph₀).div
    (((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : W × ℂ)).analyticAt _).comp
      (hD.fderiv.comp_of_eq hgraph hgraph₀))
    (by simpa only [hp₀] using hu)

/-- In particular, the residue amplitude used in the saddle calculation has
a uniform linear Taylor error on a definite neighborhood. -/
theorem residue_amplitude_linear_bound
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {A D : W × ℂ → ℂ} {p : W → ℂ}
    (hA : AnalyticAt ℂ A (0, 0)) (hD : AnalyticAt ℂ D (0, 0))
    (hp : AnalyticAt ℂ p 0) (hp₀ : p 0 = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) :
    ∃ K > 0, ∃ δ > 0, ∀ w, ‖w‖ < δ →
      ‖A (w, p w) / (fderiv ℂ D (w, p w)) (0, 1) -
        A (0, 0) / (fderiv ℂ D (0, 0)) (0, 1)‖ ≤ K * ‖w‖ := by
  simpa only [hp₀] using
    analytic_amplitude_bound (analytic_residue_amplitude hA hD hp hp₀ hu)

end Maxwell.Green
