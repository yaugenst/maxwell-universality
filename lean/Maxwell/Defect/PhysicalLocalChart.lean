import Maxwell.Defect.PhysicalLimitBounds
import Maxwell.Green.PhysicalEdge
import Maxwell.Green.Whitening

/-! The local chart is constructed from the actual finite-source projector
and the positive quadratic Taylor form of the same physical band. -/
namespace Maxwell.Defect.PhysicalLimit

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.SourceProfile
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1000000

theorem momentumTorus_eq_angular (q : Momentum) :
    TorusChart.momentumTorus q = angularTorusPoint (WithLp.ofLp q) := by
  ext j
  change (((2 * Real.pi)⁻¹ * q j : ℝ) : UnitAddCircle) =
    ((q j / (2 * Real.pi) : ℝ) : UnitAddCircle)
  congr 1
  ring

theorem realMomentum_add (θ : RealTorusCoordinates) (q : Momentum) :
    realMomentum (θ + WithLp.ofLp q) = complexifyCoordinates θ + momentumComplex q := by
  ext j
  exact Complex.ofReal_add _ _

theorem localSource_angular (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (q : Momentum) :
    localSource edges W (angularTorusPoint θ) q =
      sourceRight edges W (complexifyCoordinates θ + momentumComplex q) := by
  rw [localSource, momentumTorus_eq_angular, ← angularTorusPoint_add,
    torusSource_angular]
  rw [realMomentum_add]

theorem numerator_analytic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → FiberOperator)
    (hP : AnalyticAt ℂ P 0) :
    AnalyticAt ℝ (numerator edges W (angularTorusPoint θ)
      (fun q => P (momentumComplex q))) 0 := by
  let B := compressedNumerator
    (fun z => sourceLeft edges W (complexifyCoordinates θ + z)) P
    (fun z => sourceRight edges W (complexifyCoordinates θ + z))
  have hB : AnalyticAt ℂ B 0 := compressedNumerator_analyticAt _ _ _ _
    ((sourceLeft_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id)) hP
    ((sourceRight_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id))
  have hr : AnalyticAt ℝ (fun q => B (momentumComplexCLM q)) 0 :=
    hB.restrictScalars.comp_of_eq (momentumComplexCLM.analyticAt 0) (map_zero _)
  have he : (fun q => B (momentumComplexCLM q)) =
      numerator edges W (angularTorusPoint θ) (fun q => P (momentumComplex q)) := by
    funext q
    rw [numerator, localSource_angular, sourceCompression_apply]
    dsimp only [B, compressedNumerator, momentumComplexCLM_apply]
    have hl := sourceLeft_real_adjoint edges W (θ + WithLp.ofLp q)
    rw [realMomentum_add] at hl
    rw [hl]
  rwa [he] at hr

/-- A positive symmetric quadratic form supplies its actual continuous
linear square root, rather than an assumed factorization. -/
theorem exists_quadratic_root
    (B : Momentum →L[ℝ] Momentum →L[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x : Momentum, x ≠ 0 → 0 < B x x) :
    ∃ L : Momentum ≃L[ℝ] Momentum, ∀ q, ‖L q‖ ^ 2 = B q q := by
  obtain ⟨Q, P, hPQ, hQP, _, _, hnorm⟩ := exists_bilinear_hessian_whitening B hs hp
  have hleft : Function.LeftInverse (matrixAction P) (matrixAction Q) := by
    intro q
    have hh : matrixAction P * matrixAction Q = 1 := by
      rw [← map_mul, hPQ, map_one]
    exact congrArg (fun T : Momentum →L[ℝ] Momentum => T q) hh
  have hright : Function.RightInverse (matrixAction P) (matrixAction Q) := by
    intro q
    have hh : matrixAction Q * matrixAction P = 1 := by
      rw [← map_mul, hQP, map_one]
    exact congrArg (fun T : Momentum →L[ℝ] Momentum => T q) hh
  exact ⟨ContinuousLinearEquiv.equivOfInverse (matrixAction Q) (matrixAction P) hleft hright, hnorm⟩

/-- The actual compressed finite-source numerator and an analytic band
with a coercive Taylor form determine the normalized local edge chart. -/
theorem exists_physical_local_chart (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → FiberOperator)
    (hP : AnalyticAt ℂ P 0) (d : Momentum → ℝ)
    (p : FormalMultilinearSeries ℝ Momentum ℝ) (hd : HasFPowerSeriesAt d p 0)
    (hd0 : d 0 = 0) (heven : ∀ᶠ q in 𝓝 (0 : Momentum), d (-q) = d q)
    (B : Momentum →L[ℝ] Momentum →L[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ q, p 2 (fun _ => q) = B q q)
    (c radiusLimit : ℝ) (hc : 0 < c) (hr : 0 < radiusLimit)
    (hcoercive : ∀ q, c * ‖q‖ ^ 2 ≤ B q q) :
    ∃ C : LocalBandChart (LocalOperator (N := N)),
      C.radius ≤ radiusLimit ∧
      C.edgeNumerator = numerator edges W (angularTorusPoint θ)
        (fun q => P (momentumComplex q)) 0 ∧
      (∀ q ∈ Metric.ball 0 C.radius, C.dispersion q = d q) ∧
      (∀ ξ, 0 ≤ ξ → C.localPart ξ = ∫ q in Metric.ball 0 C.radius,
        (d q + ξ)⁻¹ • numerator edges W (angularTorusPoint θ)
          (fun q => P (momentumComplex q)) q) ∧
      (∀ ξ, 0 ≤ ξ → IntegrableOn (fun q => (d q + ξ)⁻¹ •
        numerator edges W (angularTorusPoint θ) (fun q => P (momentumComplex q)) q)
        (Metric.ball 0 C.radius)) := by
  have hpos (q : Momentum) (hq : q ≠ 0) : 0 < B q q :=
    (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hq))).trans_le (hcoercive q)
  obtain ⟨L, hL⟩ := exists_quadratic_root B hs hpos
  obtain ⟨C, hCr, _, hC0, _, hCd, hCi, hInt⟩ := exists_analytic_localBandChart
    (numerator edges W (angularTorusPoint θ) (fun q => P (momentumComplex q))) d p
    (numerator_analytic edges W θ P hP) hd hd0 heven L hc hr
    (fun q => (hp q).trans (hL q).symm)
    (fun q => (hcoercive q).trans_eq (hL q).symm)
  exact ⟨C, hCr, hC0, hCd, hCi, hInt⟩

end
end Maxwell.Defect.PhysicalLimit
