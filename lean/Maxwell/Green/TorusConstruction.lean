import Maxwell.Green.AnalyticLocalGreen
import Maxwell.Green.ChartCutoff
import Maxwell.Green.TorusAsymptotic
import Maxwell.Green.BoundaryContour

/-! Construction of the full-torus local assembly from an analytic quotient.
The localized amplitude, its regularity, and its integrability are proved
from the actual principal chart and the inverse-square bound on the original
boundary amplitude. -/

noncomputable section

open Filter MeasureTheory Set Metric WithLp
open scoped Topology ContDiff

namespace Maxwell.Green

/-- An isolated singular value does not obstruct measurability on the cube. -/
theorem aestronglyMeasurable_of_continuousAt_punctured_cube
    (H : RealTorusCoordinates → ℂ) (a p : ℝ)
    (hH : ∀ q ∈ torusCube a p, q ≠ 0 → ContinuousAt H q) :
    AEStronglyMeasurable H (torusCubeMeasure a p) := by
  have hnull : NullSingletonClass (torusCubeMeasure a p) := by
    unfold torusCubeMeasure
    infer_instance
  have hc : ContinuousOn H (torusCube a p \ {0}) := by
    intro q hq
    exact (hH q hq.1 hq.2).continuousWithinAt
  have hm := hc.aestronglyMeasurable
    ((isCompact_torusCube a p).measurableSet.diff (measurableSet_singleton 0))
    (μ := torusCubeMeasure a p)
  have hae : ∀ᵐ q ∂torusCubeMeasure a p, q ∈ torusCube a p \ {0} := by
    filter_upwards [ae_mem_torusCube a p, (torusCubeMeasure a p).ae_ne 0] with q hq hq₀
    exact ⟨hq, hq₀⟩
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm

theorem integrable_of_punctured_cube_inverseSquare
    (H : RealTorusCoordinates → ℂ) (C a p : ℝ)
    (hH : ∀ q ∈ torusCube a p, q ≠ 0 → ContinuousAt H q)
    (hbound : ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q) :
    Integrable H (torusCubeMeasure a p) := by
  have hnull : NullSingletonClass (torusCubeMeasure a p) := by
    unfold torusCubeMeasure
    infer_instance
  apply (coordinateBoundaryMajorant_integrable C a p).mono'
    (aestronglyMeasurable_of_continuousAt_punctured_cube H a p hH)
  filter_upwards [ae_mem_torusCube a p, (torusCubeMeasure a p).ae_ne 0] with q hq hq₀
  exact hbound q hq hq₀

/-- The original inverse-square bound and smooth gluing already imply
integrability of the localized singular term. -/
theorem integrable_localized_of_inverseSquare
    (H L B : RealTorusCoordinates → ℂ) (C : ℝ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hL : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ L q)
    (hB : ContDiffAt ℝ ∞ B 0)
    (hres : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] B)
    (hbound : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q) :
    Integrable L (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
  have hi := integrable_of_punctured_cube_inverseSquare H C (-Real.pi) (2 * Real.pi)
    (fun q hq hq₀ => (hH q hq hq₀).continuousAt) hbound
  have hr := localizedRemainder_smoothOnTorusCube H L B hH hL hB hres
  have hri : Integrable (localizedRemainder H L B)
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)) :=
    continuousOn_integrable_torusCube (fun q hq => (hr q hq).continuousAt.continuousWithinAt)
  apply (hi.sub hri).congr
  filter_upwards [localizedRemainder_reconstruct_ae H L B (-Real.pi) (2 * Real.pi)] with q hq
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hq)

namespace AnalyticLocalGreenData

variable {A F : (ℂ × ℂ) × ℂ → ℂ} {v q₁ q₂ : ℝ}
variable (D : AnalyticLocalGreenData A F v q₁ q₂)

def principalQuotient (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (q : RealTorusCoordinates) : ℂ :=
  realChartSlice A (T.symm q).1 (T.symm q).2 /
    realChartSlice F (T.symm q).1 (T.symm q).2

def localizedPrincipalQuotient (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (q : RealTorusCoordinates) : ℂ :=
  (principalCutoff T D.saddle.cutoff D.normalCutoffRadius q : ℂ) *
    principalQuotient (A := A) (F := F) T q

theorem localizedPrincipalQuotient_contDiffAt
    (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    {q : RealTorusCoordinates} (hq : q ≠ 0) :
    ContDiffAt ℝ ∞ (D.localizedPrincipalQuotient T) q := by
  apply contDiffAt_principalCutoff_mul T D.saddle.cutoff D.normalCutoffRadius D.cutoff_smooth
  intro hs
  obtain ⟨hw, hu⟩ := principalCutoff_tsupport_coordinates T D.saddle.cutoff
    D.normalCutoffRadius_pos (fun w hw => (D.support_bound w hw).le) hs
  have hur : |(T.symm q).2| ≤ D.normalRadius := by
    have := D.cutoffRadius_le
    have := D.normalCutoffRadius_pos
    dsimp [normalCutoffRadius] at *
    linarith
  have hpair : ((T.symm q).1, (T.symm q).2) ≠ (0, 0) := by
    intro he
    have hz : T.symm q = 0 := he
    have := congrArg T hz
    exact hq (by simpa only [T.apply_symm_apply, map_zero] using this)
  exact (D.quotient_contDiffAt hw hur hpair).comp q T.symm.contDiff.contDiffAt

theorem localizedPrincipalQuotient_eq_near_zero
    (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates) :
    D.localizedPrincipalQuotient T =ᶠ[𝓝 (0 : RealTorusCoordinates)]
      principalQuotient (A := A) (F := F) T := by
  filter_upwards [principalCutoff_one_near_zero T D.saddle.cutoff D.normalCutoffRadius_pos
    D.saddle.δ_pos D.saddle.cutoff_core] with q hq
  simp only [localizedPrincipalQuotient, hq, Complex.ofReal_one, one_mul]

/-- The full-torus assembly is constructed from the original analytic
quotient, its smooth residual germ, and the original inverse-square bound.
No cutoff regularity, integrability, integral equality, or Fourier decay
is assumed. -/
def toTorusLocalAssemblyData
    {n : Fin 3 → ℤ} (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace (integerMomentum n)))
    (H B : RealTorusCoordinates → ℂ) (C : ℝ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hB : ContDiffAt ℝ ∞ B 0)
    (hres : H =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] fun q =>
      principalQuotient (A := A) (F := F)
        (coordinatePrincipalLinearEquiv (integerMomentum n) (integerMomentum_ne_zero hn) b) q + B q)
    (hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      H (q + (2 * Real.pi) • Pi.single i 1) = H q)
    (hbound : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q)
    {η : ℝ} (hsupport : ∀ w, D.saddle.cutoff w ≠ 0 → ‖w‖ ≤ η)
    (hsmall : 2 * η + 2 * D.normalCutoffRadius < Real.pi)
    (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) : TorusLocalAssemblyData n := by
  let T := coordinatePrincipalLinearEquiv (integerMomentum n) (integerMomentum_ne_zero hn) b
  let L := D.localizedPrincipalQuotient T
  have hL : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ L q :=
    fun q _ hq => D.localizedPrincipalQuotient_contDiffAt T hq
  have he : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] B := by
    filter_upwards [hres, (D.localizedPrincipalQuotient_eq_near_zero T).filter_mono
      nhdsWithin_le_nhds] with q hq hLq
    change H q - D.localizedPrincipalQuotient T q = B q
    rw [hLq, hq]
    ring
  refine {
    direction_ne_zero := hn
    H := H
    L := L
    B := B
    smooth_H := hH
    smooth_L := hL
    smooth_B := hB
    residual := he
    support_L := ?_
    integrable_L := integrable_localized_of_inverseSquare H L B C hH hL hB he hbound
    periodic_H := hperiod
    basis := b
    saddle := D.saddle
    regular := D.regular
    numerator := realChartSlice A
    denominator := realChartSlice F
    radius := D.normalCutoffRadius
    diskRadius := D.normalRadius
    radius_pos := D.normalCutoffRadius_pos
    radius_disk := D.cutoffRadius_le
    cutoff_compact := D.cutoff_compact
    phase_small := D.phase_bound
    numerator_analytic := ?_
    denominator_analytic := ?_
    phase_root := ?_
    simple_root := ?_
    unique_root := ?_
    residue_amplitude := D.amplitude_eq
    regular_amplitude := D.regular_eq
    chart_quotient := ?_
    normalSpeed := v
    q₁ := q₁
    q₂ := q₂
    normalSpeed_pos := hv
    q₁_pos := hq₁
    q₂_pos := hq₂
    quadratic_model := D.model_eq
  }
  · exact tsupport_mul_subset_left.trans ((tsupport_comp_subset
      (show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero)
      (principalCutoff T D.saddle.cutoff D.normalCutoffRadius)).trans
      (principalCutoff_tsupport_interior _ (integerMomentum_ne_zero hn) b
        D.saddle.cutoff D.normalCutoffRadius_pos hsupport hsmall))
  · intro w hw
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.1
  · intro w hw
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.1
  · intro w hw
    rw [realChartSlice, D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.1
  · intro w hw
    rw [D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.2.1
  · intro w hw z hz hzero
    rw [D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.2.2 z hz hzero
  · intro w u
    change D.localizedPrincipalQuotient T (T (w, u)) = _
    simp only [localizedPrincipalQuotient, principalQuotient, principalCutoff_chart,
      ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_mul]

end AnalyticLocalGreenData

/-- Ordinary analytic data and the actual boundary amplitude construct the
full-torus assembly. The cutoff is chosen inside the torus here, so no
localization or asymptotic certificate is an input. -/
theorem exists_torusLocalAssemblyData_of_analytic
    {n : Fin 3 → ℤ} (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace (integerMomentum n)))
    (A F : (ℂ × ℂ) × ℂ → ℂ)
    (hA : AnalyticAt ℂ A (0, 0)) (hF : AnalyticAt ℂ F (0, 0)) (hF₀ : F (0, 0) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    (htrans : (fderiv ℂ F (0, 0)).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w)
    (H B : RealTorusCoordinates → ℂ) (C : ℝ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hB : ContDiffAt ℝ ∞ B 0)
    (hres : H =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] fun q =>
      AnalyticLocalGreenData.principalQuotient (A := A) (F := F)
        (coordinatePrincipalLinearEquiv (integerMomentum n) (integerMomentum_ne_zero hn) b) q + B q)
    (hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      H (q + (2 * Real.pi) • Pi.single i 1) = H q)
    (hbound : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q) :
    ∃ D : TorusLocalAssemblyData n,
      D.H = H ∧ D.saddle.amplitude0 = A (0, 0) / (fderiv ℂ F (0, 0)) (0, 1) ∧
      D.normalSpeed = v ∧ D.q₁ = q₁ ∧ D.q₂ = q₂ := by
  obtain ⟨D, hρ, _, hs⟩ := exists_analyticLocalGreenData_within A F hA hF hF₀ hu htrans
    hv hq₁ hq₂ (show 0 < Real.pi / 8 by positivity) hquadratic
  have hsupport (w : ℂ) (hw : D.saddle.cutoff w ≠ 0) : ‖w‖ ≤ Real.pi / 8 := by
    have := hs (subset_tsupport D.saddle.cutoff hw)
    exact (mem_ball_zero_iff.mp this).le
  have hsmall : 2 * (Real.pi / 8) + 2 * D.normalCutoffRadius < Real.pi := by
    linarith [Real.pi_pos]
  refine ⟨D.toTorusLocalAssemblyData hn b H B C hH hB hres hperiod hbound
    hsupport hsmall hv hq₁ hq₂, rfl, ?_, rfl, rfl, rfl⟩
  exact D.amplitude_zero

end Maxwell.Green
