import Maxwell.Green.TorusContour
import Maxwell.Green.Singularity

/-! Exact passage from interior torus contours to a singular boundary contour. -/

noncomputable section

open MeasureTheory Set Filter WithLp
open scoped Topology

namespace Maxwell.Green

/-- The Euclidean inverse-square majorant in ordinary torus coordinates. -/
def coordinateBoundaryMajorant (C : ℝ) (q : RealTorusCoordinates) : ℝ :=
  boundaryMajorant C (toLp 2 q)

/-- Measure preservation under the Euclidean coordinate identification
transfers the proved three-dimensional integrability to the actual cube. -/
theorem coordinateBoundaryMajorant_integrable (C a p : ℝ) :
    Integrable (coordinateBoundaryMajorant C) (torusCubeMeasure a p) := by
  have hcompact : IsCompact ((toLp 2) '' torusCube a p) :=
    (isCompact_torusCube a p).image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))
  have hint := boundaryMajorant_integrableOn C hcompact.isBounded
  have hi : IntegrableOn (coordinateBoundaryMajorant C) (torusCube a p) volume := by
    exact (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_image
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding |>.mp hint
  have hmeasure : torusCubeMeasure a p =
      volume.restrict (Set.univ.pi (fun _ : Fin 3 => Ioc a (a + p))) :=
    (Measure.restrict_pi_pi (fun _ : Fin 3 => volume) _).symm
  rw [hmeasure]
  apply hi.mono_set
  intro q hq i
  have hqi := hq i (mem_univ i)
  exact ⟨hqi.1.le, hqi.2⟩

/-- Dominated convergence on the actual torus cube. The exceptional point
is removed by its zero measure; integrability of the majorant is a theorem. -/
theorem tendsto_torus_boundary_integral
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → RealTorusCoordinates → V} {H : RealTorusCoordinates → V}
    (C a p : ℝ)
    (hmeas : ∀ᶠ t in l, AEStronglyMeasurable (F t) (torusCubeMeasure a p))
    (hbound : ∀ᶠ t in l, ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖F t q‖ ≤ coordinateBoundaryMajorant C q)
    (hlim : ∀ q ∈ torusCube a p, q ≠ 0 → Tendsto (fun t => F t q) l (𝓝 (H q))) :
    Tendsto (fun t => ∫ q, F t q ∂torusCubeMeasure a p) l
      (𝓝 (∫ q, H q ∂torusCubeMeasure a p)) := by
  have hnull : NullSingletonClass (torusCubeMeasure a p) := by
    unfold torusCubeMeasure
    infer_instance
  apply tendsto_integral_filter_of_dominated_convergence (coordinateBoundaryMajorant C) hmeas
  · filter_upwards [hbound] with t ht
    filter_upwards [ae_mem_torusCube a p, (torusCubeMeasure a p).ae_ne 0] with q hq hqne
    exact ht q hq hqne
  · exact coordinateBoundaryMajorant_integrable C a p
  · filter_upwards [ae_mem_torusCube a p, (torusCubeMeasure a p).ae_ne 0] with q hq hqne
    exact hlim q hq hqne

/-- The same majorant proves integrability of the measurable boundary
value itself, without an integrability premise on that boundary value. -/
theorem integrable_torus_boundary_limit
    {ι V : Type*} [NormedAddCommGroup V]
    {l : Filter ι} [l.NeBot]
    {F : ι → RealTorusCoordinates → V} {H : RealTorusCoordinates → V}
    (C a p : ℝ) (hH : AEStronglyMeasurable H (torusCubeMeasure a p))
    (hbound : ∀ᶠ t in l, ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖F t q‖ ≤ coordinateBoundaryMajorant C q)
    (hlim : ∀ q ∈ torusCube a p, q ≠ 0 → Tendsto (fun t => F t q) l (𝓝 (H q))) :
    Integrable H (torusCubeMeasure a p) := by
  have hnull : NullSingletonClass (torusCubeMeasure a p) := by
    unfold torusCubeMeasure
    infer_instance
  apply (coordinateBoundaryMajorant_integrable C a p).mono' hH
  filter_upwards [ae_mem_torusCube a p, (torusCubeMeasure a p).ae_ne 0] with q hq hqne
  exact le_of_tendsto (hlim q hq hqne).norm (hbound.mono fun t ht => ht q hq hqne)

theorem contourShift_rescale (β : RealTorusCoordinates) (t : ℝ) (q : RealTorusCoordinates) :
    contourShift β t q = complexifyCoordinates q + Complex.I • complexifyCoordinates (t • β) := by
  ext i
  simp only [contourShift, complexifyCoordinates, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, Complex.ofReal_mul, smul_eq_mul]
  ring

/-- Analyticity near the compact endpoint contour implies its integrability. -/
theorem integrable_analytic_interior_contour
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates) (t a p : ℝ)
    (hφ : AnalyticOnNhd ℂ φ (contourTube (t • β) a p)) :
    Integrable (fun q => φ (contourShift β t q)) (torusCubeMeasure a p) := by
  have hcont : ContinuousOn (fun q => φ (contourShift β t q)) (torusCube a p) := by
    intro q hq
    have hz : contourShift β t q ∈ contourTube (t • β) a p := by
      refine ⟨(1, q), ⟨by norm_num, hq⟩, ?_⟩
      rw [contourShift_rescale β t q]
      simp only [contourShift, one_smul]
    have hc : ContinuousAt (contourShift β t) q :=
      (continuous_contourShift β).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
    exact ((hφ _ hz).continuousAt.comp hc).continuousWithinAt
  have h := hcont.integrableOn_compact (isCompact_torusCube a p) (μ := torusCubeMeasure a p)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_torusCube a p)] at h

/-- Exact shift of the entire periodic Fourier contour onto a boundary
contour with an integrable inverse-square singularity. Analyticity supplies
each interior identity, and dominated convergence supplies its boundary limit.
The integrand `φ` may include the physical Fourier exponential. -/
theorem analytic_periodic_boundary_contour_identity
    (φ : ComplexTorusCoordinates → ℂ) (H : RealTorusCoordinates → ℂ)
    (β : RealTorusCoordinates) (C a p : ℝ) (hp : 0 ≤ p)
    (hφ : ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ φ (contourTube (t • β) a p))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      φ (z + (p : ℂ) • Pi.single i 1) = φ z)
    (hH : AEStronglyMeasurable H (torusCubeMeasure a p))
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖φ (contourShift β t q)‖ ≤ coordinateBoundaryMajorant C q)
    (hlim : ∀ q ∈ torusCube a p, q ≠ 0 →
      Tendsto (fun t => φ (contourShift β t q)) (𝓝[<] (1 : ℝ)) (𝓝 (H q))) :
    Integrable H (torusCubeMeasure a p) ∧
      (∫ q, φ (complexifyCoordinates q) ∂torusCubeMeasure a p) =
        ∫ q, H q ∂torusCubeMeasure a p := by
  have he : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ico (0 : ℝ) 1 := Ico_mem_nhdsLT zero_lt_one
  have hbe := he.mono fun t ht => hbound t ht
  have hme : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable (fun q => φ (contourShift β t q)) (torusCubeMeasure a p) :=
    he.mono fun t ht => (integrable_analytic_interior_contour φ β t a p (hφ t ht)).aestronglyMeasurable
  refine ⟨integrable_torus_boundary_limit C a p hH hbe hlim, ?_⟩
  have hlimit := tendsto_torus_boundary_integral C a p hme hbe hlim
  have hconstant : (fun t => ∫ q, φ (contourShift β t q) ∂torusCubeMeasure a p) =ᶠ[𝓝[<] (1 : ℝ)]
      fun _ => ∫ q, φ (complexifyCoordinates q) ∂torusCubeMeasure a p := by
    filter_upwards [he] with t ht
    simp_rw [contourShift_rescale]
    exact integral_analytic_periodic_contour_invariant φ (t • β) a p hp (hφ t ht) hperiod
  have hc : Tendsto (fun t => ∫ q, φ (contourShift β t q) ∂torusCubeMeasure a p)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ q, φ (complexifyCoordinates q) ∂torusCubeMeasure a p)) :=
    tendsto_const_nhds.congr' hconstant.symm
  exact tendsto_nhds_unique hc hlimit

end Maxwell.Green
