import Maxwell.Green.PhysicalFamily
import Maxwell.Green.UniformResidue

/-! Physical Green asymptotics with a source-mode-independent operating
threshold and a quantitative square-root overlap budget. -/
noncomputable section
namespace Maxwell.Green
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open PhysicalAnalytic PhysicalLower SourceProfile PhysicalCompression Filter Set Metric InnerProductSpace
open scoped Topology InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000
namespace PhysicalSimpleEdgeData
variable {material : Cell20 → ℝ} {edge : ℝ} {θ : RealTorusCoordinates}
variable (S : PhysicalSimpleEdgeData material edge θ)

theorem exists_physical_green_family_uniform {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) :
    ∃ (D : SpectralLevelBodyData S.value edge) (ξ₀ budget : ℝ), 0 < ξ₀ ∧ 0 < budget ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < ξ₀ →
      ∀ u : EuclideanSpace ℂ (Fin N), ‖u‖ = 1 →
      budget * Real.sqrt ξ <
        ‖inner ℂ S.eigenvector (sourceRight edges W (complexifyCoordinates θ) u)‖ ^ 2 →
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
  obtain ⟨rN, LN, hrN, hLN, hnumBound⟩ := exists_uniform_source_numerator_bound
    edges W θ S.projector S.projector_analytic
  obtain ⟨δR, hδR, hreflection⟩ := Metric.eventually_nhds_iff_ball.mp S.reflection.eventually_nhds
  obtain ⟨δI, hδI, hI⟩ := S.exists_complex_exclusion
  obtain ⟨δE, hδE, hE⟩ := S.exists_real_gap
  obtain ⟨δM, hδM, hmajor⟩ := exists_physical_contour_majorant_radius_uniform
    edges W material edge θ S.value S.projector S.regular S.value_analytic
    S.projector_analytic S.regular_analytic S.real_hessian_positive S.reflection
    (S.real_resolvent.mono (fun _ hz hne => (hz hne).2))
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
  let η := min δI (min δE (min δM (min δD (min δL (min rN δR)))))
  have hη : 0 < η := lt_min hδI (lt_min hδE (lt_min hδM (lt_min hδD (lt_min hδL (lt_min hrN hδR)))))
  have hηI : η ≤ δI := min_le_left _ _
  have hηE : η ≤ δE := (min_le_right _ _).trans (min_le_left _ _)
  have hηM : η ≤ δM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηD : η ≤ δD := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηL : η ≤ δL := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hηN : η ≤ rN := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hηR : η ≤ δR := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨D, hDη⟩ := exists_spectralLevelBodyData_within S.value edge
    S.value_analytic S.value_zero S.stationary S.hessian_positive hη
  let budget := LN / Real.sqrt D.quadraticConstant
  have hbudget : 0 < budget := div_pos hLN (Real.sqrt_pos.mpr D.quadraticConstant_pos)
  let ξ₀ := min (D.quadraticConstant * D.radius ^ 2) η
  have hξ₀ : 0 < ξ₀ := lt_min (mul_pos D.quadraticConstant_pos
    (sq_pos_of_pos D.radius_pos)) hη
  refine ⟨D, ξ₀, budget, hξ₀, hbudget, ?_⟩
  intro ξ hξ hξsmall u hu hoverlap
  let num := sourceNumerator edges W u θ S.projector
  have hξr : ξ < D.quadraticConstant * D.radius ^ 2 := hξsmall.trans_le (min_le_left _ _)
  have hξη : ξ < η := hξsmall.trans_le (min_le_right _ _)
  have hξabs : |ξ| < η := by rwa [abs_of_pos hξ]
  have hgap := hE ξ hξ (hξη.trans_le hηE)
  have hnum : ∀ β ∈ D.body ξ, AnalyticAt ℂ num (Complex.I • momentumComplex β) ∧
      num (Complex.I • momentumComplex β) ≠ 0 := by
    intro β hβ
    have hβball := (D.body_properties hξ hξr).2.2.2 hβ
    have hβη : ‖β.ofLp‖ < η := (norm_coordinates_le_euclidean β).trans_lt
      ((mem_ball_zero_iff.mp hβball).trans hDη)
    have hcn : ‖Complex.I • momentumComplex β‖ = ‖β.ofLp‖ := norm_imaginary_coordinates β.ofLp
    have hp : (Complex.I • momentumComplex β, ξ) ∈
        ball ((0,0) : ComplexTorusCoordinates × ℝ) δL := by
      change (Complex.I • momentumComplex β, ξ) ∈ ball (0 : ComplexTorusCoordinates × ℝ) δL
      rw [mem_ball_zero_iff, Prod.norm_def, hcn, Real.norm_eq_abs, max_lt_iff]
      exact ⟨hβη.trans_le hηL, hξabs.trans_le hηL⟩
    refine ⟨sourceNumerator_analyticAt edges W u θ _ (hlocal _ hp).1, ?_⟩
    apply sourceNumerator_ne_zero_of_budget edges W θ S.projector S.eigenvector S.projector_zero
      u (Complex.I • momentumComplex β) budget ξ _ hoverlap
    have hb := D.quadratic_lower hβ.1
    have hc := Real.sq_sqrt D.quadraticConstant_pos.le
    have hcs := Real.sqrt_pos.mpr D.quadraticConstant_pos
    have hξs := Real.sq_sqrt hξ.le
    have hn : Real.sqrt D.quadraticConstant * ‖β‖ ≤ Real.sqrt ξ := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      rw [mul_pow, hc, hξs]
      exact hb.trans hβ.2
    have hn' : ‖β‖ ≤ Real.sqrt ξ / Real.sqrt D.quadraticConstant := by
      apply (le_div_iff₀ hcs).mpr
      simpa only [mul_comm] using hn
    calc
      _ ≤ LN * ‖Complex.I • momentumComplex β‖ := hnumBound _
        (by rw [hcn]; exact hβη.trans_le hηN) u hu
      _ ≤ LN * ‖β‖ := mul_le_mul_of_nonneg_left
        (by rw [hcn]; exact norm_coordinates_le_euclidean β) hLN.le
      _ ≤ LN * (Real.sqrt ξ / Real.sqrt D.quadraticConstant) :=
        mul_le_mul_of_nonneg_left hn' hLN.le
      _ = budget * Real.sqrt ξ := by dsimp [budget]; ring
  have hreflect : ∀ β ∈ D.body ξ, ∀ᶠ z in 𝓝 (Complex.I • momentumComplex β),
      S.value (reflectedComplexCoordinates z) = conj (S.value z) := by
    intro β hβ
    apply hreflection _
    rw [mem_ball_zero_iff]
    change ‖Complex.I • complexifyCoordinates β.ofLp‖ < δR
    rw [norm_imaginary_coordinates β.ofLp]
    exact ((norm_coordinates_le_euclidean β).trans_lt
      ((mem_ball_zero_iff.mp ((D.body_properties hξ hξr).2.2.2 hβ)).trans hDη)).trans_le hηR
  have hsaddle := exists_supported_principal_saddle_on S.value num edge D ξ hξ hξr hnum hreflect
  refine ⟨hgap, ?_⟩
  intro n hn
  obtain ⟨β, χ, b, q, hβ, hlevel, hmax, hσ, hχ, hq, hjet⟩ :=
    hsaddle (integerMomentum n) (integerMomentum_ne_zero hn)
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
  obtain ⟨C, _, hbound⟩ := hmajor u ξ (hξabs.trans_le hηM) β.ofLp (hβη.trans_le hηM)
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
