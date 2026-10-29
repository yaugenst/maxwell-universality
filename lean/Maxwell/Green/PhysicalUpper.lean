import Maxwell.Green.PhysicalAnalytic

/-! Full physical weighted-block decay from invertibility of the actual
conventional fibers on an ellipsoid of simultaneous complex shifts.
Compactness supplies the bound on the same finite-source density. -/
namespace Maxwell.Green.PhysicalAnalytic

open MeasureTheory Set Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.SourceProfile Maxwell.Green.PhysicalCompression
noncomputable section
variable {N : ℕ}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The simultaneous tube stays in a centered ellipsoid, including both
contour endpoints; no rectangular continuation region is assumed. -/
theorem ellipsoid_tube_analytic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (Q : MomentumSpace →L[ℝ] MomentumSpace) (ρ : ℝ)
    (_hρ : 0 ≤ ρ)
    (hI : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ → ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)).IsInvertible)
    (β : MomentumSpace) (hβ : ‖Q β‖ ≤ ρ) :
    AnalyticOnNhd ℂ (density edges W material E) (contourTube β.ofLp (-Real.pi) (2 * Real.pi)) := by
  rintro z ⟨⟨s,q⟩, ⟨hs,hq⟩, rfl⟩
  apply density_analyticAt
  have hsβ : ‖Q (s • β)‖ ≤ ρ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖Q β‖ ≤ 1 * ρ := mul_le_mul hs.2 hβ (norm_nonneg _) (by norm_num)
      _ = ρ := one_mul _
  have hp : contourShift β.ofLp s q =
      complexifyCoordinates q + Complex.I • complexifyCoordinates (s • β).ofLp := by
    funext j
    simp only [contourShift, complexifyCoordinates, Pi.add_apply, Pi.smul_apply,
      PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
    ring
  change (shiftedOperator material E (contourShift β.ofLp s q)).IsInvertible
  rw [hp]
  exact hI (s • β) hsβ q hq

/-- A compact ellipsoid and the actual resolvent imply one finite density
bound, independent of the propagation direction and separation. -/
theorem exists_ellipsoid_density_bound (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (P Q : MomentumSpace →L[ℝ] MomentumSpace)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x) (ρ : ℝ)
    (hI : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ → ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)).IsInvertible) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        ‖density edges W material E (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)‖ ≤ C := by
  let mapPoint := fun p : MomentumSpace × RealTorusCoordinates =>
    complexifyCoordinates p.2 + Complex.I • complexifyCoordinates (P p.1).ofLp
  have hmap : Continuous mapPoint := by
    change Continuous (fun p : MomentumSpace × RealTorusCoordinates =>
      fun j => (p.2 j : ℂ) + Complex.I * (P p.1 j : ℂ))
    fun_prop
  have hc : ContinuousOn (fun p : MomentumSpace × RealTorusCoordinates =>
      density edges W material E (mapPoint p))
      ((Metric.closedBall (0 : MomentumSpace) ρ) ×ˢ torusCube (-Real.pi) (2 * Real.pi)) := by
    intro p hp
    have hn : ‖Q (P p.1)‖ ≤ ρ := by simpa only [hQP, mem_closedBall_zero_iff] using hp.1
    exact ((density_analyticAt edges W material E (mapPoint p) (hI (P p.1) hn p.2 hp.2)).continuousAt.comp
      hmap.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : MomentumSpace) ρ).prod
    (isCompact_torusCube (-Real.pi) (2 * Real.pi))).exists_bound_of_continuousOn hc
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ q hq
  have hh := hC (Q β, q) ⟨by simpa only [mem_closedBall_zero_iff] using hβ, hq⟩
  dsimp only [mapPoint] at hh
  rw [hPQ] at hh
  exact hh.trans (le_max_right _ _)

/-- The actual infinite weighted resolvent block has a uniform exponential
operator-norm bound in the inverse-Hessian metric. -/
theorem physical_block_ellipsoid_upper (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (P Q : MomentumSpace →L[ℝ] MomentumSpace)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hI : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ → ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)).IsInvertible) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Site,
      ‖weightedBlock edges W
        (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material)) K hK hm -
          (E : ℂ) • 1)) n‖ ≤ C * Real.exp (-ρ * ‖P (integerMomentum n)‖) := by
  obtain ⟨C, hC, hb⟩ := exists_ellipsoid_density_bound edges W material E P Q hPQ hQP ρ hI
  refine ⟨C, hC, ?_⟩
  intro n
  have h := block_ellipsoid_fourier_upper (density edges W material E) n P Q hQP hsym ρ hρ C
    (ellipsoid_tube_analytic edges W material E Q ρ hρ hI) (density_periodic edges W material E) hb
  have hid := weightedBlock_density_integral edges W material K hK hm E hE n 1
  simp only [Nat.cast_one, one_mul] at hid
  rw [hid]
  have hphase (q : RealTorusCoordinates) : torusFourierFactor 1 n q =
      complexFourierFactor n (complexifyCoordinates q) := by
    simp [torusFourierFactor, oscillatoryFactor, complexFourierFactor, complexifyCoordinates]
  simp only [hphase]
  have hscale (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      (1 / (2 * Real.pi)^3 : ℝ) • T = ((2 * Real.pi : ℂ)^3)⁻¹ • T := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change ((1 / (2 * Real.pi)^3 : ℝ) : ℂ) * T x i = ((2 * Real.pi : ℂ)^3)⁻¹ * T x i
    norm_num
  rw [hscale]
  exact h

end
end Maxwell.Green.PhysicalAnalytic
