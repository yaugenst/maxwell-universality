import Maxwell.Green.PhysicalEdge

/-! The support point, actual scalar torus assembly, contour identity and
nonzero residue are constructed together from the same physical edge. -/

noncomputable section

namespace Maxwell.Green

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open PhysicalAnalytic PhysicalLower SourceProfile PhysicalCompression Filter Set Metric InnerProductSpace
open scoped Topology InnerProductSpace ComplexConjugate

set_option maxHeartbeats 800000

theorem scalar_contour_analytic_of_interior {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ) (E : ℝ)
    (u : EuclideanSpace ℂ (Fin N)) (θ β : RealTorusCoordinates)
    (hI : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates θ + contourShift β t q)).IsInvertible) :
    ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ (scalarDensity edges W material E u θ)
      (contourTube (t • β) (-Real.pi) (2 * Real.pi)) := by
  intro t ht z hz
  obtain ⟨⟨s, q⟩, ⟨hs, hq⟩, rfl⟩ := hz
  apply scalarDensity_analyticAt
  have hst : s * t ∈ Ico (0 : ℝ) 1 :=
    ⟨mul_nonneg hs.1 ht.1, (mul_le_of_le_one_left ht.1 hs.2).trans_lt ht.2⟩
  have he : contourShift (t • β) s q = contourShift β (s * t) q := by
    ext j
    simp only [contourShift, complexifyCoordinates, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  change (shiftedOperator material E
    (complexifyCoordinates θ + contourShift (t • β) s q)).IsInvertible
  rw [he]
  exact hI (s * t) hst q hq

namespace PhysicalSimpleEdgeData

variable {material : Cell20 → ℝ} {edge : ℝ} {θ : RealTorusCoordinates}
variable (S : PhysicalSimpleEdgeData material edge θ)

/-- For every sufficiently small operating shift and every integer
direction, the actual weighted lattice block has the constructed full
torus saddle representation with a nonzero residue. -/
theorem exists_physical_green_family {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (u : EuclideanSpace ℂ (Fin N))
    (hoverlap : inner ℂ S.eigenvector
      (sourceRight edges W (complexifyCoordinates θ) u) ≠ 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) :
    ∃ (D : SpectralLevelBodyData S.value edge) (ξ₀ : ℝ), 0 < ξ₀ ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < ξ₀ →
      (∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t)) ∧
      ∀ n : Site, n ≠ 0 → ∃ (β : MomentumSpace) (A : TorusLocalAssemblyData n),
        β ∈ ball (0 : MomentumSpace) D.radius ∧
        imaginaryMomentumLevel S.value edge β = ξ ∧
        IsMaxOn (fun x => inner ℝ (integerMomentum n) x) (D.body ξ) β ∧
        0 < inner ℝ (integerMomentum n) β ∧ A.saddle.amplitude0 ≠ 0 ∧
        ∀ d : ℕ,
          inner ℂ u (weightedBlock edges W
            (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
              K hK hm - ((edge - ξ : ℝ) : ℂ) • 1)) (fun i => (d : ℤ) * n i) u) =
            A.fullScalarGreen (integerPairingCLM n θ) (inner ℝ (integerMomentum n) β) d := by
  let num := sourceNumerator edges W u θ S.projector
  have hnumA : AnalyticAt ℂ num 0 := sourceNumerator_analyticAt edges W u θ _ S.projector_analytic
  have hnum₀ : num 0 ≠ 0 := by
    rw [show num 0 = (‖inner ℂ S.eigenvector
      (sourceRight edges W (complexifyCoordinates θ) u)‖ ^ 2 : ℝ) from
        sourceNumerator_zero edges W u θ _ _ S.projector_zero]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hoverlap))
  obtain ⟨δI, hδI, hI⟩ := S.exists_complex_exclusion
  obtain ⟨δE, hδE, hE⟩ := S.exists_real_gap
  obtain ⟨δM, hδM, hmajor⟩ := S.exists_majorant_radius edges W u
  obtain ⟨δD, CD, hδD, hCD, hden⟩ := analytic_edge_denominator_control S.value S.value_analytic
    S.real_hessian_positive S.reflection
  have hnearP : ∀ᶠ z in 𝓝 ((0,0) : ComplexTorusCoordinates × ℝ), AnalyticAt ℂ S.projector z.1 :=
    continuous_fst.continuousAt.tendsto.eventually S.projector_analytic.eventually_analyticAt
  have hnearR : ∀ᶠ z in 𝓝 ((0,0) : ComplexTorusCoordinates × ℝ),
      AnalyticAt ℂ S.regular (z.1, (-z.2 : ℂ)) := by
    have hc : Continuous (fun z : ComplexTorusCoordinates × ℝ => (z.1, (-z.2 : ℂ))) := by fun_prop
    exact (hc.continuousAt (x := (0,0))).tendsto.eventually
      (by simpa using S.regular_analytic.eventually_analyticAt)
  obtain ⟨δL, hδL, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp
    (hnearP.and (hnearR.and S.real_resolvent.eventually_nhds))
  let η := min δI (min δE (min δM (min δD δL)))
  have hη : 0 < η := lt_min hδI (lt_min hδE (lt_min hδM (lt_min hδD hδL)))
  have hηI : η ≤ δI := min_le_left _ _
  have hηE : η ≤ δE := (min_le_right _ _).trans (min_le_left _ _)
  have hηM : η ≤ δM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηD : η ≤ δD := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηL : η ≤ δL := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨D, hDη, hsaddle⟩ := exists_supported_principal_saddle_within S.value num edge
    S.value_analytic hnumA hnum₀ S.value_zero S.stationary S.hessian_positive S.reflection hη
  let ξ₀ := min (D.quadraticConstant * D.radius ^ 2) η
  have hξ₀ : 0 < ξ₀ := lt_min (mul_pos D.quadraticConstant_pos
    (sq_pos_of_pos D.radius_pos)) hη
  refine ⟨D, ξ₀, hξ₀, ?_⟩
  intro ξ hξ hξsmall
  have hξr : ξ < D.quadraticConstant * D.radius ^ 2 := hξsmall.trans_le (min_le_left _ _)
  have hξη : ξ < η := hξsmall.trans_le (min_le_right _ _)
  have hξabs : |ξ| < η := by rwa [abs_of_pos hξ]
  have hgap := hE ξ hξ (hξη.trans_le hηE)
  refine ⟨hgap, ?_⟩
  intro n hn
  obtain ⟨β, χ, b, q, hβ, hlevel, hmax, hσ, hχ, hq, hjet⟩ :=
    hsaddle ξ hξ hξr (integerMomentum n) (integerMomentum_ne_zero hn)
  have hβclosed := ball_subset_closedBall hβ
  have hβbody : β ∈ D.body ξ := ⟨hβclosed, hlevel.le⟩
  have hβη : ‖β.ofLp‖ < η :=
    (norm_coordinates_le_euclidean β).trans_lt ((mem_ball_zero_iff.mp hβ).trans hDη)
  have hβcomplex : momentumComplex β = complexifyCoordinates β.ofLp := rfl
  let center := Complex.I • momentumComplex β
  have hcenter : ‖center‖ = ‖β.ofLp‖ := norm_imaginary_coordinates β.ofLp
  have hpair : (center, ξ) ∈ ball ((0,0) : ComplexTorusCoordinates × ℝ) δL := by
    change (center, ξ) ∈ ball (0 : ComplexTorusCoordinates × ℝ) δL
    rw [mem_ball_zero_iff, Prod.norm_def, hcenter, Real.norm_eq_abs, max_lt_iff]
    exact ⟨hβη.trans_le hηL, hξabs.trans_le hηL⟩
  obtain ⟨hPcenter, hRcenter, hresNear⟩ := hlocal (center, ξ) hpair
  have hRξ : AnalyticAt ℂ (fun z => S.regular (z, (-ξ : ℂ))) center :=
    AnalyticAt.comp (g := S.regular) (f := fun z => (z, (-ξ : ℂ))) hRcenter
      (analyticAt_id.prod analyticAt_const)
  have hpole : ∀ᶠ z in 𝓝 center, S.value z - ((edge - ξ : ℝ) : ℂ) ≠ 0 →
      (shiftedOperator material (edge - ξ) (complexifyCoordinates θ + z)).inverse =
        (S.value z - ((edge - ξ : ℝ) : ℂ))⁻¹ • S.projector z + S.regular (z, (-ξ : ℂ)) := by
    have ht : Tendsto (fun z : ComplexTorusCoordinates => (z, ξ)) (𝓝 center) (𝓝 (center, ξ)) :=
      continuousAt_id.tendsto.prodMk_nhds tendsto_const_nhds
    filter_upwards [ht.eventually hresNear] with z hz hne
    exact (hz (sub_ne_zero.mp hne)).2
  have hnumcenter : num center ≠ 0 := by
    simpa only [affineDenominator, map_zero, add_zero, sub_zero] using hjet.2.1
  have hvaluecenter : S.value center = ((edge - ξ : ℝ) : ℂ) := by
    have hf := hjet.2.2.2.1
    simpa only [affineDenominator, map_zero, add_zero, sub_eq_zero] using hf
  obtain ⟨hboundaryI, hinteriorI⟩ := physical_contour_invertibility_of_body material edge θ
    S.value D δI (hDη.trans_le hηI) hI hξ (hξη.trans_le hηI) hβbody
  have hboundary : ∀ x ∈ torusCube (-Real.pi) (2 * Real.pi), x ≠ 0 →
      (shiftedOperator material (edge - ξ)
        (complexifyCoordinates θ + (center + complexifyCoordinates x))).IsInvertible := by
    intro x hx hx₀
    have h := hboundaryI 1 (by norm_num) x hx hx₀
    simpa only [contourShift, one_smul, add_comm, center, hβcomplex] using h
  have hdenGerm : ∀ᶠ x in 𝓝 (0 : RealTorusCoordinates), x ≠ 0 →
      S.value (center + complexifyCoordinates x) - ((edge - ξ : ℝ) : ℂ) ≠ 0 ∧
      ‖(S.value (center + complexifyCoordinates x) - ((edge - ξ : ℝ) : ℂ))⁻¹‖ ≤
        CD * inverseSquare (WithLp.toLp 2 x) := by
    have hn : ∀ᶠ x in 𝓝 (0 : RealTorusCoordinates), ‖WithLp.toLp 2 x‖ < δD :=
      ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).norm.continuousAt).eventually
        (gt_mem_nhds (by simpa using hδD))
    filter_upwards [hn] with x hx hx₀
    have h := hden x β.ofLp hx (hβη.trans_le hηD) hx₀ (edge - ξ)
      (by rw [show Complex.I • complexifyCoordinates β.ofLp = center from rfl, hvaluecenter]; simp)
    simpa only [center, hβcomplex, add_comm] using h
  have hv : 0 < χ * ‖integerMomentum n‖ := mul_pos hχ
    (norm_pos_iff.mpr (integerMomentum_ne_zero hn))
  obtain ⟨A, hAH, _, hAnonzero, _, _, _⟩ := exists_physical_torus_assembly edges W material
    (edge - ξ) u θ S.value S.projector (fun z => S.regular (z, (-ξ : ℂ))) center
    hPcenter hRξ hnumcenter hn b (χ * ‖integerMomentum n‖) (q 0) (q 1) hv (hq 0) (hq 1)
    hjet.2.2.1 hvaluecenter hjet.2.2.2.2.1 hjet.2.2.2.2.2.1
    (by simpa only [hjet.2.2.2.2.1] using hjet.2.2.2.2.2.2)
    hpole hboundary CD hCD.le hdenGerm
  have hlevelgap : ∀ t ∈ Icc (0 : ℝ) 1,
      edge - ξ ≤ (S.value (Complex.I • complexifyCoordinates (t • β.ofLp))).re := by
    intro t ht
    have hl := D.level_smul_le hβclosed ht
    have hm := mul_le_of_le_one_left hξ.le ht.2
    rw [hlevel] at hl
    change edge - (S.value (Complex.I • momentumComplex (t • β))).re ≤ t * ξ at hl
    change edge - ξ ≤ (S.value (Complex.I • momentumComplex (t • β))).re
    linarith
  obtain ⟨C, _, hbound⟩ := hmajor ξ (hξabs.trans_le hηM) β.ofLp (hβη.trans_le hηM)
    hlevelgap hboundaryI
  refine ⟨β, A, hβ, hlevel, hmax, hσ, hAnonzero, ?_⟩
  intro d
  rw [integerMomentum_inner] at hσ ⊢
  apply weightedBlock_eq_fullScalarGreen edges W material K hK hm (edge - ξ) hgap u θ β.ofLp A hσ.le
    (scalar_contour_analytic_of_interior edges W material (edge - ξ) u θ β.ofLp hinteriorI)
    (fun x hx hx₀ => (scalarDensity_analyticAt edges W material (edge - ξ) u θ
      (hboundaryI 1 (by norm_num) x hx hx₀)).continuousAt) C
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩)
  intro x _ _
  rw [hAH]
  simp only [contourShift, one_smul, center, hβcomplex, add_comm]

end PhysicalSimpleEdgeData

end Maxwell.Green
