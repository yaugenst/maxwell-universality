import Maxwell.Defect.PhysicalRayleigh
import Maxwell.Defect.CoherentCubeProfile
import Maxwell.Defect.LocalBandLimit

/-! Physical-coordinate lower bounds without extending a local eigenbranch
to a globally chosen torus eigenbasis. -/
namespace Maxwell.Defect

open MeasureTheory Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.PhysicalCompression

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

theorem centered_ball_integral_lower (A b : Torus → ℝ)
    (hA : Integrable A) (hb : Integrable b)
    (pole : Momentum → ℝ) (center : Torus) {r : ℝ} (hr : r ≤ Real.pi)
    (hpole : IntegrableOn pole (Metric.ball 0 r))
    (hlower : ∀ q ∈ TorusChart.physicalCell,
      (Metric.ball (0 : Momentum) r).indicator pole q -
        b (center + Bloch.momentumTorus q) ≤ A (center + Bloch.momentumTorus q)) :
    (∫ q in Metric.ball 0 r, pole q) / (2 * Real.pi) ^ 3 - ∫ t, b t ≤ ∫ t, A t := by
  have hmap (q : Momentum) : TorusChart.momentumTorus q = Bloch.momentumTorus q := by
    ext i
    simp only [TorusChart.momentumTorus, TorusChart.quotient, Bloch.momentumTorus,
      PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hA' : Integrable A TorusChart.haar := hA
  have hb' : Integrable b TorusChart.haar := hb
  have hAc : IntegrableOn (fun q => A (center + TorusChart.momentumTorus q))
      TorusChart.physicalCell := TorusChart.integrable_physicalCell _
        (((measurePreserving_add_left TorusChart.haar center).integrable_comp hA'.aestronglyMeasurable).mpr hA')
  have hbc : IntegrableOn (fun q => b (center + TorusChart.momentumTorus q))
      TorusChart.physicalCell := TorusChart.integrable_physicalCell _
        (((measurePreserving_add_left TorusChart.haar center).integrable_comp hb'.aestronglyMeasurable).mpr hb')
  have hpi : IntegrableOn ((Metric.ball (0 : Momentum) r).indicator pole)
      TorusChart.physicalCell :=
    (hpole.integrable_indicator measurableSet_ball).integrableOn
  have hI := integral_mono_ae (hpi.sub hbc) hAc (by
    filter_upwards [ae_restrict_mem TorusChart.measurableSet_physicalCell] with q hq
    simpa only [hmap, Pi.sub_apply] using hlower q hq)
  simp only [Pi.sub_apply] at hI
  rw [integral_sub hpi hbc, setIntegral_indicator measurableSet_ball,
    Set.inter_eq_right.mpr (TorusChart.ball_subset_physicalCell hr)] at hI
  have hscale := mul_le_mul_of_nonneg_left hI
    (show 0 ≤ (1 / (2 * Real.pi) ^ 3 : ℝ) by positivity)
  rw [mul_sub] at hscale
  have hiA := TorusChart.integral_centered_physicalCell A hA'.aestronglyMeasurable center
  have hib := TorusChart.integral_centered_physicalCell b hb'.aestronglyMeasurable center
  simp only [smul_eq_mul] at hiA hib
  rw [← hiA, ← hib] at hscale
  rw [show TorusChart.haar = (volume : Measure Torus) from rfl] at hscale
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hscale

set_option maxHeartbeats 800000 in
/-- The local selected-band eigenvector is needed only inside the physical
ball. Every other spectral component is controlled by the actual global gap. -/
theorem physical_inverse_centered_ball_lower (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z g : ℝ) (hg : 0 < g)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ t : Torus, ∀ s ∈ spectrum ℝ (torusElectric m t), s ≤ z - g ∨ z ≤ s)
    (center : Torus) {r : ℝ} (hr : r ≤ Real.pi)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (lam : Momentum → ℝ)
    (hupper : ∀ q ∈ Metric.ball 0 r, z < lam q)
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1)
    (heig : ∀ q : Momentum, q ∈ Metric.ball 0 r →
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric m (center + Bloch.momentumTorus q)) (φ q) = (lam q : ℂ) • φ q)
    (hpole : IntegrableOn (fun q => ‖inner ℂ (φ q)
      (WithLp.toLp 2 (profile edges a (center + Bloch.momentumTorus q)))‖ ^ 2 / (lam q - z))
      (Metric.ball 0 r)) :
    (∫ q in Metric.ball 0 r, ‖inner ℂ (φ q)
      (WithLp.toLp 2 (profile edges a (center + Bloch.momentumTorus q)))‖ ^ 2 / (lam q - z)) /
        (2 * Real.pi) ^ 3 - ‖finiteField edges a‖ ^ 2 / g ≤
      (inner ℂ (finiteField edges a)
        (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)
          (finiteField edges a))).re := by
  have hI := centered_ball_integral_lower
    (fun t => (scalarAmplitude edges a m z t).re)
    (fun t => ‖WithLp.toLp 2 (profile edges a t)‖ ^ 2 / g)
    (scalarAmplitude_integrable edges a m z hz).re
    ((profile_vector_integrable_norm_sq edges a).div_const g)
    _ center hr hpole (by
      intro q _
      by_cases hq : q ∈ Metric.ball (0 : Momentum) r
      · rw [Set.indicator_of_mem hq]
        exact matrixResolvent_selected_lower _ (torusElectric_hermitian m _) z g (lam q)
          hg (hz _) (hgap _) (hupper q hq) (φ q) (hunit q hq) (heig q hq) _
      · rw [Set.indicator_of_notMem hq, zero_sub]
        exact matrixResolvent_lower _ (torusElectric_hermitian m _) z g hg (hz _) (hgap _) _)
  rw [integral_div, profile_vector_parseval] at hI
  have hreal : (∫ t : Torus, (scalarAmplitude edges a m z t).re) =
      (∫ t : Torus, scalarAmplitude edges a m z t).re :=
    integral_re (scalarAmplitude_integrable edges a m z hz)
  rw [hreal] at hI
  have hidentity := scalarCoupling_integral edges a m K hK hm z hz 0
  have heq : translateEdge 0 ∘ edges = edges := by
    funext i
    simp only [Function.comp_apply, translateEdge, smul_zero, sub_zero, Prod.mk.eta]
  simp only [scalarCoupling, heq, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul] at hidentity
  rw [hidentity]
  exact hI

end
end Maxwell.Defect
