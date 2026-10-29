import Maxwell.Defect.PhysicalRegularConstruction

/-! The physical local and far resolvent bounds imply the actual integral
remainder estimate, including integrability at the edge energy. -/
namespace Maxwell.Defect.PhysicalLimit
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.AnalyticEigenbranch
open Maxwell.Green Maxwell.Green.SourceProfile
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1000000

theorem regularDensity_integrable (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (θ : RealTorusCoordinates) (P : Momentum → FiberOperator)
    (edge radius ξ : ℝ)
    (hP : ∀ q ∈ Metric.closedBall 0 radius, ContinuousAt P q)
    (hi : ∀ q ∈ Metric.closedBall 0 radius,
      (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
        ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible) :
    IntegrableOn (regularDensity edges W (PeriodicYee.edgeAverage material)
      (angularTorusPoint θ) P edge ξ) (Metric.ball 0 radius) := by
  have hc : ContinuousOn (regularDensity edges W (PeriodicYee.edgeAverage material)
      (angularTorusPoint θ) P edge ξ) (Metric.closedBall 0 radius) := by
    intro q hq
    have hr := regularResolvent_continuousAt
      (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ)) P edge q ξ
      (fiber_continuous material θ).continuousAt (hP q hq) (hi q hq)
    have hs : ContinuousAt (fun p : Momentum =>
        regularResolvent (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) p)
          (P p) ((edge - ξ : ℝ) : ℂ)) q :=
      hr.comp (f := fun p : Momentum => (p, ξ)) (continuousAt_id.prodMk continuousAt_const)
    have hJ := (localSource_continuous edges W θ).continuousAt (x := q)
    have hh := (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hJ).clm_comp
      (hs.clm_comp hJ)
    change ContinuousWithinAt (fun p =>
      (localSource edges W (angularTorusPoint θ) p).adjoint.comp
        ((regularResolvent (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) p)
          (P p) ((edge : ℂ) - ξ)).comp (localSource edges W (angularTorusPoint θ) p)))
      (Metric.closedBall 0 radius) q
    simpa only [Complex.ofReal_sub, Function.comp_apply] using hh.continuousWithinAt
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall

theorem fullDensity_integrable (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (θ : RealTorusCoordinates) (E radius : ℝ)
    (hi : ∀ q ∈ closedPhysicalCell \ Metric.ball 0 radius,
      (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q - (E : ℂ) • 1).IsInvertible) :
    IntegrableOn (fullDensity edges W (PeriodicYee.edgeAverage material)
      (angularTorusPoint θ) E) (TorusChart.physicalCell \ Metric.ball 0 radius) := by
  have hc : ContinuousOn (fullDensity edges W (PeriodicYee.edgeAverage material)
      (angularTorusPoint θ) E) (closedPhysicalCell \ Metric.ball 0 radius) := by
    intro q hq
    have hi' : ContinuousAt (fun A : FiberOperator => A.inverse)
        (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q - (E : ℂ) • 1) :=
      (ComplexContourGap.analyticAt_inverse_operator (hi q hq)).continuousAt
    have hh := (sourceMap_continuous edges W θ).continuousAt.clm_apply
      (hi'.comp (f := fun p => fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) p - (E : ℂ) • 1)
        ((fiber_continuous material θ).continuousAt.sub continuousAt_const))
    exact hh.continuousWithinAt
  exact (hc.integrableOn_compact (closedPhysicalCell_compact.diff Metric.isOpen_ball)).mono_set
    (sdiff_subset_sdiff_left physicalCell_subset_closed)

theorem exists_sourceMap_bound (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ closedPhysicalCell, ‖sourceMap edges W (angularTorusPoint θ) q‖ ≤ C := by
  have hc : ContinuousOn (fun q => ‖sourceMap edges W (angularTorusPoint θ) q‖)
      closedPhysicalCell :=
    ((@continuous_norm (FiberOperator →L[ℝ] LocalOperator (N := N)) inferInstance).comp
      (sourceMap_continuous edges W θ)).continuousOn
  obtain ⟨C, hC⟩ := closedPhysicalCell_compact.exists_bound_of_continuousOn hc
  refine ⟨max C 0 + 1, by positivity, fun q hq => ?_⟩
  have hh := hC q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (sourceMap edges W (angularTorusPoint θ) q))] at hh
  exact hh.trans (show C ≤ max C 0 + 1 by linarith [le_max_left C 0])

/-- Compactness provides the source weight, continuity provides all four
integrability statements, and actual resolvent identities give the linear
energy error. -/
theorem regularPart_bound_from_uniform (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (θ : RealTorusCoordinates) (P : Momentum → FiberOperator)
    (edge radius r Cl Cf : ℝ) (hradius : radius ≤ Real.pi) (hr : 0 < r)
    (hCl : 0 < Cl) (hCf : 0 < Cf)
    (hP : ∀ q ∈ Metric.closedBall 0 radius, ContinuousAt P q)
    (halg : ∀ q ∈ Metric.ball 0 radius, P q * P q = P q ∧
      P q * fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q =
        fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q * P q)
    (hlocal : ∀ ξ : ℝ, 0 ≤ ξ → ξ < r → ∀ q ∈ Metric.closedBall 0 radius,
      (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
        ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible ∧
      ‖regularResolvent (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q)
        (P q) ((edge - ξ : ℝ) : ℂ)‖ ≤ Cl)
    (hfar : ∀ ξ : ℝ, 0 ≤ ξ → ξ < r → ∀ q ∈ closedPhysicalCell \ Metric.ball 0 radius,
      (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
        ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
        ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ Cf) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ξ : ℝ, 0 ≤ ξ → ξ < r →
      ‖regularPart edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ) P edge radius 0 -
        regularPart edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ) P edge radius ξ‖ ≤ L * ξ := by
  obtain ⟨Cw, hCw, hw⟩ := exists_sourceMap_bound edges W θ
  let g := (Cl + Cf)⁻¹
  have hg : 0 < g := by dsimp [g]; positivity
  have hgi : g⁻¹ = Cl + Cf := inv_inv _
  have hwl : IntegrableOn (fun _ : Momentum => Cw) (Metric.ball 0 radius) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : Momentum) radius)).mono_set
      Metric.ball_subset_closedBall
  have hwf : IntegrableOn (fun _ : Momentum => Cw)
      (TorusChart.physicalCell \ Metric.ball 0 radius) :=
    (continuousOn_const.integrableOn_compact closedPhysicalCell_compact).mono_set
      (fun _ hq => physicalCell_subset_closed hq.1)
  let L := (((∫ q in Metric.ball (0 : Momentum) radius, Cw) +
      ∫ q in TorusChart.physicalCell \ Metric.ball 0 radius, Cw) / g ^ 2)
  refine ⟨max L 0, le_max_right _ _, fun ξ hξ hξr => ?_⟩
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left L 0) hξ)
  apply regularPart_difference_bound edges W (PeriodicYee.edgeAverage material)
    (angularTorusPoint θ) P edge radius ξ g hg hξ (fun _ => Cw)
  · exact regularDensity_integrable edges W material θ P edge radius 0 hP
      (fun q hq => (hlocal 0 le_rfl hr q hq).1)
  · exact regularDensity_integrable edges W material θ P edge radius ξ hP
      (fun q hq => (hlocal ξ hξ hξr q hq).1)
  · exact fullDensity_integrable edges W material θ edge radius
      (fun q hq => by simpa only [sub_zero] using (hfar 0 le_rfl hr q hq).1)
  · exact fullDensity_integrable edges W material θ (edge - ξ) radius
      (fun q hq => (hfar ξ hξ hξr q hq).1)
  · exact hwl
  · exact hwf
  · intro q hq
    have hq' := Metric.ball_subset_closedBall hq
    obtain ⟨hi0, hn0⟩ := hlocal 0 le_rfl hr q hq'
    obtain ⟨hiξ, hnξ⟩ := hlocal ξ hξ hξr q hq'
    simp only [sub_zero] at hi0 hn0
    refine ⟨(halg q hq).1, (halg q hq).2, hi0, hiξ, ?_, ?_, ?_⟩
    · rw [hgi]; exact hn0.trans (by linarith)
    · rw [hgi]; exact hnξ.trans (by linarith)
    · exact hw q (physicalCell_subset_closed (TorusChart.ball_subset_physicalCell hradius hq))
  · intro q hq
    have hq' : q ∈ closedPhysicalCell \ Metric.ball 0 radius :=
      ⟨physicalCell_subset_closed hq.1, hq.2⟩
    obtain ⟨hi0, hn0⟩ := hfar 0 le_rfl hr q hq'
    obtain ⟨hiξ, hnξ⟩ := hfar ξ hξ hξr q hq'
    simp only [sub_zero] at hi0 hn0
    refine ⟨hi0, hiξ, ?_, ?_, hw q hq'.1⟩
    · rw [hgi]; exact hn0.trans (by linarith)
    · rw [hgi]; exact hnξ.trans (by linarith)

end
end Maxwell.Defect.PhysicalLimit
