import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-!
# Simultaneous periodic contour deformation

The parameter differentiates a whole contour at once. Consequently the
result requires bounds only along the chosen path and its local neighborhoods;
it does not require the coordinate box joining the endpoints to be admissible.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Maxwell.Green

/-- A periodic spatial derivative has zero integral over a period. -/
theorem periodic_slice_integral_deriv_eq_zero
    {f f' : ℝ → ℂ} {a p : ℝ}
    (hderiv : ∀ x ∈ uIcc a (a + p), HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a (a + p))
    (hperiod : f (a + p) = f a) :
    (∫ x in a..a + p, f' x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hperiod, sub_self]

/-- Fubini lifts cancellation of one periodic spatial derivative to the
whole periodic integration domain. The other coordinates are represented by
an arbitrary sigma-finite measure, so this applies to each torus coordinate. -/
theorem periodic_flux_integral_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {f f' : ℝ → α → ℂ} {a p : ℝ} (hp : 0 ≤ p)
    (hderiv : ∀ q x, x ∈ uIcc a (a + p) →
      HasDerivAt (fun x => f x q) (f' x q) x)
    (hint : Integrable (fun z : ℝ × α => f' z.1 z.2)
      ((volume.restrict (Ioc a (a + p))).prod μ))
    (hperiod : ∀ q, f (a + p) q = f a q) :
    (∫ z : ℝ × α, f' z.1 z.2
      ∂((volume.restrict (Ioc a (a + p))).prod μ)) = 0 := by
  have hap : a ≤ a + p := le_add_of_nonneg_right hp
  rw [integral_prod_symm _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [hint.prod_left_ae] with q hq
  rw [← intervalIntegral.integral_of_le hap]
  exact periodic_slice_integral_deriv_eq_zero (hderiv q)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hap).mpr hq) (hperiod q)

/-- The slice assumptions only need to hold almost everywhere in the other
coordinates. This applies directly to a compact periodic cube. -/
theorem periodic_flux_integral_eq_zero_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {f f' : ℝ → α → ℂ} {a p : ℝ} (hp : 0 ≤ p)
    (hderiv : ∀ᵐ q ∂μ, ∀ x ∈ uIcc a (a + p),
      HasDerivAt (fun x => f x q) (f' x q) x)
    (hint : Integrable (fun z : ℝ × α => f' z.1 z.2)
      ((volume.restrict (Ioc a (a + p))).prod μ))
    (hperiod : ∀ᵐ q ∂μ, f (a + p) q = f a q) :
    (∫ z : ℝ × α, f' z.1 z.2
      ∂((volume.restrict (Ioc a (a + p))).prod μ)) = 0 := by
  have hap : a ≤ a + p := le_add_of_nonneg_right hp
  rw [integral_prod_symm _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [hint.prod_left_ae, hderiv, hperiod] with q hq hd hpq
  rw [← intervalIntegral.integral_of_le hap]
  exact periodic_slice_integral_deriv_eq_zero hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hap).mpr hq) hpq

/-- A finite sum of periodic spatial fluxes has integral zero. The slice
version above and Fubini establish each `hflux` in a periodic box. -/
theorem integral_sum_flux_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι] (weight : ι → ℂ) (flux : ι → α → ℂ)
    (hint : ∀ i, Integrable (flux i) μ)
    (hflux : ∀ i, (∫ q, flux i q ∂μ) = 0) :
    (∫ q, ∑ i, weight i * flux i q ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (hint i).const_mul (weight i))]
  simp_rw [integral_const_mul, hflux, mul_zero]
  simp

/-- Whole-contour invariance from local differentiation under the integral.
`F'` is the derivative along the simultaneous path. Its vanishing integral
is supplied by the periodic flux lemma, after the Cauchy--Riemann identity.
All differentiation and domination premises are local around each parameter.
-/
theorem contour_integral_invariant
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F F' : ℝ → α → ℂ) {a b : ℝ}
    (hlocal : ∀ s ∈ uIcc a b, ∃ (N : Set ℝ) (bound : α → ℝ),
      N ∈ 𝓝 s ∧
      (∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) μ) ∧
      Integrable (F s) μ ∧ AEStronglyMeasurable (F' s) μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, ‖F' t q‖ ≤ bound q) ∧
      Integrable bound μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, HasDerivAt (fun t => F t q) (F' t q) t))
    (hzero : ∀ s ∈ uIcc a b, (∫ q, F' s q ∂μ) = 0) :
    (∫ q, F b q ∂μ) = ∫ q, F a q ∂μ := by
  have hderiv : ∀ s ∈ uIcc a b,
      HasDerivAt (fun t => ∫ q, F t q ∂μ) 0 s := by
    intro s hs
    obtain ⟨N, bound, hN, hmeas, hint, hmeas', hbound, hbint, hdiff⟩ := hlocal s hs
    have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hN hmeas hint hmeas' hbound hbint hdiff).2
    simpa only [hzero s hs] using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
  simpa only [intervalIntegral.integral_zero, eq_comm, sub_eq_zero] using hFTC

end Maxwell.Green
