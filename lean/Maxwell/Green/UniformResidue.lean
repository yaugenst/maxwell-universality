import Maxwell.Green.PhysicalEdge

/-! A quantitative source-residue bound uniform over unit defect modes.
The budget is selected before the operating energy and mode. -/
noncomputable section
namespace Maxwell.Green.PhysicalLower
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open SourceProfile Filter Metric Set InnerProductSpace
open scoped Topology ContDiff InnerProductSpace
set_option maxHeartbeats 600000

variable {N : ℕ}

def operatorNumerator (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField)
    (z : ComplexTorusCoordinates) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Defect.compressedNumerator
    (fun w => sourceLeft edges W (complexifyCoordinates θ + w)) P
    (fun w => sourceRight edges W (complexifyCoordinates θ + w)) z

theorem operatorNumerator_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField)
    {z : ComplexTorusCoordinates} (hP : AnalyticAt ℂ P z) :
    AnalyticAt ℂ (operatorNumerator edges W θ P) z := by
  apply Defect.compressedNumerator_analyticAt
  · exact (sourceLeft_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id)
  · exact hP
  · exact (sourceRight_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id)

theorem sourceNumerator_sub_norm_le (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) (hu : ‖u‖ = 1)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField)
    (z w : ComplexTorusCoordinates) :
    ‖sourceNumerator edges W u θ P z - sourceNumerator edges W u θ P w‖ ≤
      ‖operatorNumerator edges W θ P z - operatorNumerator edges W θ P w‖ := by
  change ‖scalarOperatorReadout u (operatorNumerator edges W θ P z) -
    scalarOperatorReadout u (operatorNumerator edges W θ P w)‖ ≤ _
  rw [← map_sub, scalarOperatorReadout_apply]
  calc
    _ ≤ ‖u‖ * ‖(operatorNumerator edges W θ P z - operatorNumerator edges W θ P w) u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖operatorNumerator edges W θ P z - operatorNumerator edges W θ P w‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by rw [hu, one_mul, mul_one]

/-- The entire physical finite source is included in the Lipschitz
estimate; it is uniform over all unit source vectors. -/
theorem exists_uniform_source_numerator_bound (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) (P : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField)
    (hP : AnalyticAt ℂ P 0) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧ ∀ z : ComplexTorusCoordinates, ‖z‖ < r →
      ∀ u : EuclideanSpace ℂ (Fin N), ‖u‖ = 1 →
        ‖sourceNumerator edges W u θ P z - sourceNumerator edges W u θ P 0‖ ≤ L * ‖z‖ := by
  have ha := operatorNumerator_analyticAt edges W θ P hP
  obtain ⟨L, U, hU, hLip⟩ := ((ha.contDiffAt : ContDiffAt ℂ ∞ (operatorNumerator edges W θ P) 0).hasStrictFDerivAt (by simp)).exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, (L : ℝ) + 1, hr, by positivity, ?_⟩
  intro z hz u hu
  calc
    _ ≤ ‖operatorNumerator edges W θ P z - operatorNumerator edges W θ P 0‖ :=
      sourceNumerator_sub_norm_le edges W u hu θ P z 0
    _ ≤ (L : ℝ) * ‖z‖ := by
      simpa only [sub_zero] using hLip.norm_sub_le (hball (mem_ball_zero_iff.mpr hz))
        (mem_of_mem_nhds hU)
    _ ≤ ((L : ℝ) + 1) * ‖z‖ := by nlinarith [norm_nonneg z]

/-- A linear `sqrt ξ` budget defeats the motion of the support point for
any unit source mode, without a mode-continuity hypothesis. -/
theorem sourceNumerator_ne_zero_of_budget
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (θ : RealTorusCoordinates)
    (P : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField)
    (φ : ConventionalField) (hP₀ : P 0 = rankOne ℂ φ φ)
    (u : EuclideanSpace ℂ (Fin N)) (z : ComplexTorusCoordinates)
    (budget ξ : ℝ)
    (hvariation : ‖sourceNumerator edges W u θ P z - sourceNumerator edges W u θ P 0‖ ≤
      budget * Real.sqrt ξ)
    (hoverlap : budget * Real.sqrt ξ <
      ‖inner ℂ φ (sourceRight edges W (complexifyCoordinates θ) u)‖ ^ 2) :
    sourceNumerator edges W u θ P z ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg, sourceNumerator_zero edges W u θ P φ hP₀,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hvariation
  linarith

end Maxwell.Green.PhysicalLower
