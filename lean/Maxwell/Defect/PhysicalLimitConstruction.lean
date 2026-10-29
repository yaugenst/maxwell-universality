import Maxwell.Defect.PhysicalRegularIntegral

/-! Construction of the actual edge compression limit from one physical
spectral branch. Every integral and remainder is discharged internally. -/
namespace Maxwell.Defect.PhysicalLimit
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.SourceProfile
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1600000

theorem exists_physical_limit_data (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (edge : ℝ) (θ : RealTorusCoordinates)
    (S : PhysicalSimpleEdgeData material edge θ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K)
    (d : Momentum → ℝ) (p : FormalMultilinearSeries ℝ Momentum ℝ)
    (hd : HasFPowerSeriesAt d p 0) (hd0 : d 0 = 0)
    (heven : ∀ᶠ q in 𝓝 (0 : Momentum), d (-q) = d q)
    (B : Momentum →L[ℝ] Momentum →L[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ q, p 2 (fun _ => q) = B q q)
    (c : ℝ) (hc : 0 < c) (hcoercive : ∀ q, c * ‖q‖ ^ 2 ≤ B q q)
    (halg : ∀ᶠ q : Momentum in 𝓝 0,
      let P := S.projector (momentumComplex q)
      let T := fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q
      P * P = P ∧ T * P = ((edge + d q : ℝ) : ℂ) • P ∧
        P * T = ((edge + d q : ℝ) : ℂ) • P)
    (hi0 : (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) 0 -
      (edge : ℂ) • 1 + S.projector 0).IsInvertible) :
    ∃ (C : LocalBandChart (LocalOperator (N := N))) (L r : ℝ),
      0 ≤ L ∧ 0 < r ∧ C.radius ≤ Real.pi ∧
      C.edgeNumerator = numerator edges W (angularTorusPoint θ)
        (fun q => S.projector (momentumComplex q)) 0 ∧
      (∀ q ∈ Metric.ball 0 C.radius, C.dispersion q = d q) ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < r →
        compression edges W (PeriodicYee.edgeAverage material) K hK hm (edge - ξ) =
          (1 / (2 * Real.pi)^3 : ℝ) • (C.localPart ξ +
            regularPart edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
              (fun q => S.projector (momentumComplex q)) edge C.radius ξ)) ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ < r →
        ‖regularPart edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
          (fun q => S.projector (momentumComplex q)) edge C.radius 0 -
          regularPart edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
          (fun q => S.projector (momentumComplex q)) edge C.radius ξ‖ ≤ L * ξ) := by
  let T := fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
  let P := fun q : Momentum => S.projector (momentumComplex q)
  have hPa : AnalyticAt ℝ P 0 :=
    S.projector_analytic.restrictScalars.comp_of_eq (momentumComplexCLM.analyticAt 0)
      (map_zero momentumComplexCLM)
  have hPi : (T 0 - (edge : ℂ) • 1 + P 0).IsInvertible := by
    simpa only [T, P, show momentumComplex (0 : Momentum) = 0 from map_zero momentumComplexCLM] using hi0
  obtain ⟨rl, Cl, hrl, hCl, hl⟩ := exists_local_regular_bounds T P edge
    (fiber_continuous material θ).continuousAt hPa.continuousAt hPi
  obtain ⟨ra, hra, ha⟩ := Metric.eventually_nhds_iff_ball.mp
    (halg.and hPa.eventually_continuousAt)
  let cutoff := min Real.pi (min rl ra) / 2
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  obtain ⟨C, hCr, hC0, hCd, hCi, hInt⟩ := exists_physical_local_chart edges W θ
    S.projector S.projector_analytic d p hd hd0 heven B hs hp c cutoff hc hcutoff hcoercive
  have hCrπ : C.radius ≤ Real.pi := hCr.trans (by
    dsimp [cutoff]
    linarith [min_le_left Real.pi (min rl ra), Real.pi_pos])
  have hCrl : C.radius < rl := hCr.trans_lt (by
    dsimp [cutoff]
    have hh := (min_le_right Real.pi (min rl ra)).trans (min_le_left rl ra)
    linarith)
  have hCra : C.radius < ra := hCr.trans_lt (by
    dsimp [cutoff]
    have hh := (min_le_right Real.pi (min rl ra)).trans (min_le_right rl ra)
    linarith)
  have hqa (q : Momentum) (hq : q ∈ Metric.closedBall 0 C.radius) :
      q ∈ Metric.ball 0 ra := by
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hq).trans_lt hCra)
  have hql (q : Momentum) (hq : q ∈ Metric.closedBall 0 C.radius) : ‖q‖ < rl :=
    (mem_closedBall_zero_iff.mp hq).trans_lt hCrl
  have hPc (q : Momentum) (hq : q ∈ Metric.closedBall 0 C.radius) : ContinuousAt P q :=
    (ha q (hqa q hq)).2
  obtain ⟨rf, Cf, hrf, hCf, hf⟩ := exists_far_inverse_bounds material edge θ C.radius
    C.radius_pos S.real_exclusion
  obtain ⟨rg, hrg, hg⟩ := S.exists_real_gap
  let r := min rl (min rf rg)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrl' : r ≤ rl := min_le_left _ _
  have hrf' : r ≤ rf := (min_le_right _ _).trans (min_le_left _ _)
  have hrg' : r ≤ rg := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal (ξ : ℝ) (hξ : 0 ≤ ξ) (hξr : ξ < r)
      (q : Momentum) (hq : q ∈ Metric.closedBall 0 C.radius) :
      (T q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible ∧
        ‖Spectral.AnalyticEigenbranch.regularResolvent (T q) (P q) ((edge - ξ : ℝ) : ℂ)‖ ≤ Cl :=
    hl q (hql q hq) ξ (by rw [abs_of_nonneg hξ]; exact hξr.trans_le hrl')
  have hfar (ξ : ℝ) (hξ : 0 ≤ ξ) (hξr : ξ < r) :=
    hf ξ (by rw [abs_of_nonneg hξ]; exact hξr.trans_le hrf')
  obtain ⟨L, hL, hreg⟩ := regularPart_bound_from_uniform edges W material θ P edge C.radius r Cl Cf
    hCrπ hr hCl hCf hPc
    (fun q hq => by
      have hh := (ha q (hqa q (Metric.ball_subset_closedBall hq))).1
      exact ⟨hh.1, hh.2.2.trans hh.2.1.symm⟩) hlocal hfar
  refine ⟨C, L, r, hL, hr, hCrπ, hC0, hCd, ?_, hreg⟩
  intro ξ hξ hξr
  have hE := hg ξ hξ (hξr.trans_le hrg')
  apply compression_decomposition edges W (PeriodicYee.edgeAverage material) K hK hm
    (angularTorusPoint θ) P d edge ξ C hCrπ hE
  · intro q hq
    have hq' := Metric.ball_subset_closedBall hq
    have hh := (ha q (hqa q hq')).1
    apply torusBlock_pole edges W (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
      P d edge ξ q hE hh.1 hh.2.1 hh.2.2 (hlocal ξ hξ.le hξr q hq').1
    have hdq : 0 ≤ d q := by
      by_cases hz : q = 0
      · simp only [hz, hd0, le_refl]
      · rw [← hCd q hq]
        exact (mul_nonneg C.coercivity_pos.le (sq_nonneg _)).trans (C.dispersion_coercive q hq hz)
    linarith
  · exact hCi ξ hξ.le
  · exact hInt ξ hξ.le
  · exact regularDensity_integrable edges W material θ P edge C.radius ξ hPc
      (fun q hq => (hlocal ξ hξ.le hξr q hq).1)

end
end Maxwell.Defect.PhysicalLimit
