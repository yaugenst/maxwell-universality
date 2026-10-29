import Maxwell.Defect.CoherentCubeEstimate
import Maxwell.Defect.CenteredRayleigh

/-! The concrete coherent source has an arbitrarily large limiting
Rayleigh quotient, from the actual lattice inverse and local band. -/
namespace Maxwell.Defect.ScalarDefect

open Spectral Spectral.Lattice Spectral.Bloch MeasureTheory Filter Topology
open Maxwell.Green.PhysicalCompression

noncomputable section

def cubeQuadratic (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20) (center : Torus)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ) : ℝ :=
  let f := finiteField (edgeEmbedding (cube L)) (coherentLatticeCoefficients L φ₀ center)
  (inner ℂ f (Ring.inverse
    (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1) f)).re

theorem cubeQuadratic_eq_compressed_real (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ∀ r, (φ₀ r).im = 0) (center : Torus) (hcenter : center + center = 0)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ) :
    cubeQuadratic L φ₀ center m K hK hm z =
      let w := realCoordinatePart (coherentCoordinates L φ₀ (fun n => UnitAddTorus.mFourier n center))
      inner ℝ w (realPartOperator (sourceCompression (injection (cube L))
        (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1))) w) := by
  dsimp only
  rw [realPartOperator_apply, realCoordinatePart_inner_right,
    coherentCoordinates_real_at_trim L φ₀ hφ₀ center hcenter]
  rw [sourceCompression_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, cubeQuadratic, coherent_finiteField]

theorem cubeQuadratic_tendsto_of_compression_tendsto (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ∀ r, (φ₀ r).im = 0) (center : Torus) (hcenter : center + center = 0)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℕ → ℝ)
    (S₀ : EuclideanSpace ℝ (Fin (edges (cube L)).card) →L[ℝ]
      EuclideanSpace ℝ (Fin (edges (cube L)).card))
    (hS : Tendsto (fun n => realPartOperator (sourceCompression (injection (cube L))
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z n : ℂ) • 1))))
      atTop (𝓝 S₀)) :
    let w := realCoordinatePart (coherentCoordinates L φ₀ (fun n => UnitAddTorus.mFourier n center))
    Tendsto (fun n => cubeQuadratic L φ₀ center m K hK hm (z n)) atTop (𝓝 (inner ℝ w (S₀ w))) := by
  dsimp only
  simp_rw [cubeQuadratic_eq_compressed_real L φ₀ hφ₀ center hcenter]
  exact tendsto_const_nhds.inner
    (((ContinuousLinearMap.apply ℝ _ (realCoordinatePart
      (coherentCoordinates L φ₀ (fun n => UnitAddTorus.mFourier n center)))).continuous.tendsto _).comp hS)

set_option maxHeartbeats 800000 in
theorem cubeQuadratic_pole_lower (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ‖φ₀‖ = 1) (center : Torus) (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (edge g : ℝ) (hg : 0 < g)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (d : Momentum → ℝ)
    {r c ξ : ℝ} (hr : r ≤ Real.pi) (hc : 0 < c) (hξ : 0 < ξ)
    (hz : ∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ t : Torus, ∀ s ∈ spectrum ℝ (torusElectric m t),
      s ≤ edge - ξ - g ∨ edge - ξ ≤ s)
    (hφ : ContinuousOn φ (Metric.ball 0 r))
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1)
    (heig : ∀ q : Momentum, q ∈ Metric.ball 0 r →
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric m (center + Bloch.momentumTorus q)) (φ q) =
          (edge + d q : ℂ) • φ q)
    (hd : Measurable d) (hnonneg : ∀ q ∈ Metric.ball 0 r, 0 ≤ d q)
    (hlower : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q) :
    (∫ q in Metric.ball 0 r, ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / (d q + ξ)) /
      (2 * Real.pi) ^ 3 - cubeMass L φ₀ / g ≤
        cubeQuadratic L φ₀ center m K hK hm (edge - ξ) := by
  have hid (q : Momentum) : edge + d q - (edge - ξ) = d q + ξ := by ring
  have hpole := coherent_shifted_pole_integrable L φ₀ hφ₀ φ d hc hξ.le hφ hunit hd hlower
  have h := physical_inverse_centered_ball_lower (edgeEmbedding (cube L))
    (coherentLatticeCoefficients L φ₀ center) m K hK hm (edge - ξ) g hg hz hgap center hr
    φ (fun q => edge + d q) (fun q hq => by linarith [hnonneg q hq]) hunit
    (fun q hq => by simpa only [Complex.ofReal_add] using heig q hq)
    (by simpa only [coherent_profile_overlap, hid] using hpole)
  simp only [coherent_profile_overlap, hid] at h
  have hcost := div_le_div_of_nonneg_right (coherent_finiteField_norm_sq_le L φ₀ center) hg.le
  change _ ≤ cubeQuadratic L φ₀ center m K hK hm (edge - ξ) at h
  linarith

set_option maxHeartbeats 800000 in
/-- Passing the actual shifted inverse to its edge limit preserves the
coherent pole lower bound. No value or lower bound of the edge compression
is assumed. -/
theorem cubeQuadratic_limit_pole_lower (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ‖φ₀‖ = 1) (center : Torus) (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (edge g : ℝ) (hg : 0 < g)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (d : Momentum → ℝ)
    {r c : ℝ} (hr : r ≤ Real.pi) (hc : 0 < c)
    (hφ : ContinuousOn φ (Metric.ball 0 r))
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1)
    (heig : ∀ q : Momentum, q ∈ Metric.ball 0 r →
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric m (center + Bloch.momentumTorus q)) (φ q) =
          (edge + d q : ℂ) • φ q)
    (hd : Measurable d) (hnonneg : ∀ q ∈ Metric.ball 0 r, 0 ≤ d q)
    (hlower : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (ξ : ℕ → ℝ) (hξ : ∀ n, 0 < ξ n) (hξlim : Tendsto ξ atTop (𝓝 0))
    (hz : ∀ n (t : Torus), edge - ξ n ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ n (t : Torus), ∀ s ∈ spectrum ℝ (torusElectric m t),
      s ≤ edge - ξ n - g ∨ edge - ξ n ≤ s)
    (Q₀ : ℝ) (hQ : Tendsto (fun n => cubeQuadratic L φ₀ center m K hK hm (edge - ξ n))
      atTop (𝓝 Q₀)) :
    (∫ q in Metric.ball 0 r, ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / d q) /
      (2 * Real.pi) ^ 3 - cubeMass L φ₀ / g ≤ Q₀ := by
  have hp := coherent_pole_tendsto_zero L φ₀ hφ₀ φ d hc hφ hunit hd hlower
    ξ (fun n => (hξ n).le) hξlim
  have hpl := (hp.div_const ((2 * Real.pi) ^ 3)).sub_const (cubeMass L φ₀ / g)
  exact le_of_tendsto_of_tendsto' hpl hQ (fun n => cubeQuadratic_pole_lower L φ₀ hφ₀
    center m K hK hm edge g hg φ d hr hc (hξ n) (hz n) (hgap n) hφ hunit heig hd hnonneg hlower)

set_option maxHeartbeats 800000 in
/-- A sufficiently large concrete scalar cube has the strict high
Rayleigh quotient needed by branch selection, for the actual compressed
inverse limit. The lower bound is derived from its coherent local pole. -/
theorem coherent_cube_high_rayleigh (L : ℕ) (hL : 8 ≤ L)
    (φ₀ : EuclideanSpace ℂ Edge20) (hφ₀ : ‖φ₀‖ = 1)
    (hφreal : ∀ r, (φ₀ r).im = 0) (center : Torus) (hcenter : center + center = 0)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (edge g threshold : ℝ) (hg : 0 < g)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (d : Momentum → ℝ)
    {r c dmax C : ℝ} (hr : 0 < r) (hc : 0 < c) (hdmax : 0 < dmax) (hC : 0 ≤ C)
    (hrsmall : r ≤ 1 / 64) (hrC : r ≤ 1 / (64 * (1 + C)))
    (hlarge : threshold < (r / (80 * dmax)) * (L : ℝ) ^ 2 - 1 / g)
    (hφ : ContinuousOn φ (Metric.ball 0 (r / L)))
    (hunit : ∀ q ∈ Metric.ball 0 (r / L), ‖φ q‖ = 1)
    (hvariation : ∀ q ∈ Metric.ball 0 (r / L), ‖φ q - φ₀‖ ≤ C * ‖q‖)
    (heig : ∀ q : Momentum, q ∈ Metric.ball 0 (r / L) →
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric m (center + Bloch.momentumTorus q)) (φ q) =
          (edge + d q : ℂ) • φ q)
    (hd : Measurable d) (hnonneg : ∀ q ∈ Metric.ball 0 (r / L), 0 ≤ d q)
    (hlower : ∀ q ∈ Metric.ball 0 (r / L), q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hupper : ∀ q ∈ Metric.ball 0 (r / L), d q ≤ dmax * ‖q‖ ^ 2)
    (ξ : ℕ → ℝ) (hξ : ∀ n, 0 < ξ n) (hξlim : Tendsto ξ atTop (𝓝 0))
    (hz : ∀ n (t : Torus), edge - ξ n ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ n (t : Torus), ∀ s ∈ spectrum ℝ (torusElectric m t),
      s ≤ edge - ξ n - g ∨ edge - ξ n ≤ s)
    (S₀ : EuclideanSpace ℝ (Fin (edges (cube L)).card) →L[ℝ]
      EuclideanSpace ℝ (Fin (edges (cube L)).card))
    (hS : Tendsto (fun n => realPartOperator (sourceCompression (injection (cube L))
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - ((edge - ξ n : ℝ) : ℂ) • 1))))
      atTop (𝓝 S₀)) :
    let w := realCoordinatePart (coherentCoordinates L φ₀ (fun n => UnitAddTorus.mFourier n center))
    threshold * ‖w‖ ^ 2 < inner ℝ w (S₀ w) := by
  let w := realCoordinatePart (coherentCoordinates L φ₀ (fun n => UnitAddTorus.mFourier n center))
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hrpi : r / (L : ℝ) ≤ Real.pi := by
    have hh := div_le_self hr.le hL1
    linarith [Real.pi_gt_three]
  have hQ := cubeQuadratic_tendsto_of_compression_tendsto L φ₀ hφreal center hcenter
    m K hK hm (fun n => edge - ξ n) S₀ hS
  have hlow := cubeQuadratic_limit_pole_lower L φ₀ hφ₀ center m K hK hm edge g hg
    φ d hrpi hc hφ hunit heig hd hnonneg hlower ξ hξ hξlim hz hgap
      (inner ℝ w (S₀ w)) hQ
  have hpole := coherent_cube_pole_lower L hL φ₀ hφ₀ φ d hr hc hdmax hC hrsmall hrC
    hφ hunit hvariation hd hlower hupper
  have hmass := (cubeMass_bounds L (by omega) φ₀ hφ₀).1
  have hmasspos : 0 < cubeMass L φ₀ := (pow_pos hLpos 3).trans_le hmass
  have hquot := coherent_cube_rayleigh_lower hLpos hmass hr hdmax hg
    (show (cubeMass L φ₀) ^ 2 * r / (8 * Real.pi ^ 2 * dmax * L) -
      cubeMass L φ₀ / g ≤ inner ℝ w (S₀ w) by linarith)
  have hw : ‖w‖ ^ 2 = cubeMass L φ₀ := by
    rw [← realCoordinateEmbedding.norm_map,
      coherentCoordinates_real_at_trim L φ₀ hφreal center hcenter]
    exact coherentCoordinates_norm_sq _ _ _ (fun n => mFourier_apply_norm n center)
  change threshold * ‖w‖ ^ 2 < inner ℝ w (S₀ w)
  rw [hw]
  exact (lt_div_iff₀ hmasspos).mp (hlarge.trans_le hquot)

end
end Maxwell.Defect.ScalarDefect
