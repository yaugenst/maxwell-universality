import Maxwell.Green.ContourPi
import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Deformation of an analytic periodic three-dimensional contour

Compactness supplies the domination needed to differentiate the contour
integral. Holomorphy turns that derivative into spatial fluxes, which cancel
on opposite periodic faces.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Maxwell.Green

private theorem integrable_of_compact_support_ae
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {f : α → ℂ} (hf : ContinuousOn f K) : Integrable f μ := by
  have h := hf.integrableOn_compact hK (μ := μ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

/-- Compactness converts pointwise local joint regularity into the uniform
local bound used by differentiation under the integral sign. -/
theorem compact_contour_local_data
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (F F' : ℝ → α → ℂ) (s : ℝ)
    (hcont : ∀ q ∈ K, ContinuousAt (Function.uncurry F') (s, q))
    (hreg : ∀ q ∈ K, ∀ᶠ z : ℝ × α in 𝓝 (s, q),
      ContinuousAt (Function.uncurry F) z ∧
      HasDerivAt (fun t => F t z.2) (F' z.1 z.2) z.1) :
    ∃ (N : Set ℝ) (bound : α → ℝ),
      N ∈ 𝓝 s ∧
      (∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) μ) ∧
      Integrable (F s) μ ∧ AEStronglyMeasurable (F' s) μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, ‖F' t q‖ ≤ bound q) ∧
      Integrable bound μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, HasDerivAt (fun t => F t q) (F' t q) t) := by
  have hslice : ContinuousOn (F' s) K := by
    intro q hq
    exact ((hcont q hq).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hslice).isBounded.exists_norm_le
  have he : ∀ᶠ t in 𝓝 s, ∀ q ∈ K,
      ContinuousAt (Function.uncurry F) (t, q) ∧
      HasDerivAt (fun t => F t q) (F' t q) t ∧ ‖F' t q‖ ≤ C + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    have hlt : ‖F' s q‖ < C + 1 := lt_of_le_of_lt (hC _ (mem_image_of_mem _ hq)) (lt_add_one C)
    have he' : ∀ᶠ z : ℝ × α in 𝓝 (s, q), ‖F' z.1 z.2‖ < C + 1 :=
      ((hcont q hq).norm).eventually (gt_mem_nhds hlt)
    filter_upwards [hreg q hq, he'] with z hz hz'
    exact ⟨hz.1, hz.2, hz'.le⟩
  let N := {t | ∀ q ∈ K, ContinuousAt (Function.uncurry F) (t, q) ∧
    HasDerivAt (fun t => F t q) (F' t q) t ∧ ‖F' t q‖ ≤ C + 1}
  have hN : N ∈ 𝓝 s := he
  have hF : ∀ t ∈ N, Integrable (F t) μ := by
    intro t ht
    apply integrable_of_compact_support_ae hK hμ
    intro q hq
    exact (((ht q hq).1).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  refine ⟨N, fun _ => C + 1, hN, ?_, hF s (mem_of_mem_nhds hN),
    (integrable_of_compact_support_ae hK hμ hslice).aestronglyMeasurable, ?_,
    integrable_const _, ?_⟩
  · filter_upwards [hN] with t ht using (hF t ht).aestronglyMeasurable
  · filter_upwards [hμ] with q hq
    exact fun t ht => (ht q hq).2.2
  · filter_upwards [hμ] with q hq
    exact fun t ht => (ht q hq).2.1

abbrev RealTorusCoordinates := Fin 3 → ℝ
abbrev ComplexTorusCoordinates := Fin 3 → ℂ

def complexifyCoordinates (q : RealTorusCoordinates) : ComplexTorusCoordinates :=
  fun i => (q i : ℂ)

def contourShift (β : RealTorusCoordinates) (s : ℝ) (q : RealTorusCoordinates) :
    ComplexTorusCoordinates := complexifyCoordinates q + s • (Complex.I • complexifyCoordinates β)

def contourParameterDerivative (φ : ComplexTorusCoordinates → ℂ)
    (β : RealTorusCoordinates) (s : ℝ) (q : RealTorusCoordinates) : ℂ :=
  fderiv ℂ φ (contourShift β s q) (Complex.I • complexifyCoordinates β)

theorem continuous_contourShift (β : RealTorusCoordinates) :
    Continuous (fun z : ℝ × RealTorusCoordinates => contourShift β z.1 z.2) := by
  unfold contourShift complexifyCoordinates
  fun_prop

theorem hasDerivAt_contourShift (β q : RealTorusCoordinates) (s : ℝ) :
    HasDerivAt (fun t => contourShift β t q) (Complex.I • complexifyCoordinates β) s := by
  apply hasDerivAt_pi.mpr
  intro i
  change HasDerivAt (fun t => (q i : ℂ) + t • (Complex.I * (β i : ℂ)))
    (Complex.I * (β i : ℂ)) s
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id s).smul_const (Complex.I * (β i : ℂ))).const_add (q i : ℂ)

theorem hasDerivAt_analytic_contour
    (φ : ComplexTorusCoordinates → ℂ) (β q : RealTorusCoordinates) (s : ℝ)
    (hφ : AnalyticAt ℂ φ (contourShift β s q)) :
    HasDerivAt (fun t => φ (contourShift β t q))
      (contourParameterDerivative φ β s q) s := by
  exact (hφ.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
    (hasDerivAt_contourShift β q s)

theorem continuousAt_analytic_contourDerivative
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (z : ℝ × RealTorusCoordinates) (hφ : AnalyticAt ℂ φ (contourShift β z.1 z.2)) :
    ContinuousAt (fun z : ℝ × RealTorusCoordinates =>
      contourParameterDerivative φ β z.1 z.2) z := by
  have hd := (hφ.contDiffAt (n := 2)).continuousAt_fderiv (by norm_num)
  exact (hd.comp (x := z) (continuous_contourShift β).continuousAt).clm_apply continuousAt_const

/-- Analyticity on one compact contour supplies all local integral data. -/
theorem analytic_contour_local_data
    {μ : Measure RealTorusCoordinates} [IsFiniteMeasure μ]
    {K : Set RealTorusCoordinates} (hK : IsCompact K)
    (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates) (s : ℝ)
    (hφ : ∀ q ∈ K, AnalyticAt ℂ φ (contourShift β s q)) :
    ∃ (N : Set ℝ) (bound : RealTorusCoordinates → ℝ),
      N ∈ 𝓝 s ∧
      (∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun q => φ (contourShift β t q)) μ) ∧
      Integrable (fun q => φ (contourShift β s q)) μ ∧
      AEStronglyMeasurable (contourParameterDerivative φ β s) μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, ‖contourParameterDerivative φ β t q‖ ≤ bound q) ∧
      Integrable bound μ ∧
      (∀ᵐ q ∂μ, ∀ t ∈ N, HasDerivAt (fun t => φ (contourShift β t q))
        (contourParameterDerivative φ β t q) t) := by
  apply compact_contour_local_data hK hμ
  · intro q hq
    exact continuousAt_analytic_contourDerivative φ β (s, q) (hφ q hq)
  · intro q hq
    have he := ((continuous_contourShift β).continuousAt (x := (s, q))).eventually
      (hφ q hq).eventually_analyticAt
    filter_upwards [he] with z hz
    exact ⟨hz.continuousAt.comp (x := z) (continuous_contourShift β).continuousAt,
      hasDerivAt_analytic_contour φ β z.2 z.1 hz⟩

def torusCube (a p : ℝ) : Set RealTorusCoordinates :=
  {q | ∀ i, q i ∈ Icc a (a + p)}

def torusCubeMeasure (a p : ℝ) : Measure RealTorusCoordinates :=
  Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc a (a + p)))

def contourTube (β : RealTorusCoordinates) (a p : ℝ) : Set ComplexTorusCoordinates :=
  (fun z : ℝ × RealTorusCoordinates => contourShift β z.1 z.2) ''
    (Icc 0 1 ×ˢ torusCube a p)

instance torusCubeMeasure_finite (a p : ℝ) : IsFiniteMeasure (torusCubeMeasure a p) := by
  unfold torusCubeMeasure
  infer_instance

theorem isCompact_torusCube (a p : ℝ) : IsCompact (torusCube a p) :=
  isCompact_pi_infinite fun _ => isCompact_Icc

theorem isCompact_contourTube (β : RealTorusCoordinates) (a p : ℝ) :
    IsCompact (contourTube β a p) :=
  (isCompact_Icc.prod (isCompact_torusCube a p)).image (continuous_contourShift β)

theorem ae_pi_interval_mem_closed_cube (n : ℕ) (a p : ℝ) :
    ∀ᵐ q ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioc a (a + p)))),
      ∀ i, q i ∈ Icc a (a + p) := by
  apply eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually
    ((ae_restrict_mem measurableSet_Ioc).mono fun _ h => ⟨h.1.le, h.2⟩)

theorem ae_mem_torusCube (a p : ℝ) :
    ∀ᵐ q ∂torusCubeMeasure a p, q ∈ torusCube a p :=
  ae_pi_interval_mem_closed_cube 3 a p

def contourSpatialFlux (φ : ComplexTorusCoordinates → ℂ)
    (β : RealTorusCoordinates) (s : ℝ) (i : Fin 3) (q : RealTorusCoordinates) : ℂ :=
  fderiv ℂ φ (contourShift β s q) (Pi.single i 1)

theorem continuousAt_analytic_spatialFlux
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (s : ℝ) (i : Fin 3) (q : RealTorusCoordinates)
    (hφ : AnalyticAt ℂ φ (contourShift β s q)) :
    ContinuousAt (contourSpatialFlux φ β s i) q := by
  have hd := (hφ.contDiffAt (n := 2)).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (contourShift β s) q :=
    (continuous_contourShift β).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
  exact (hd.comp hc).clm_apply continuousAt_const

theorem integrable_contourSpatialFlux
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (a p s : ℝ) (i : Fin 3)
    (hφ : ∀ q ∈ torusCube a p, AnalyticAt ℂ φ (contourShift β s q)) :
    Integrable (contourSpatialFlux φ β s i) (torusCubeMeasure a p) := by
  apply integrable_of_compact_support_ae (isCompact_torusCube a p) (ae_mem_torusCube a p)
  intro q hq
  exact (continuousAt_analytic_spatialFlux φ β s i q (hφ q hq)).continuousWithinAt

theorem hasDerivAt_contour_coordinate
    (β : RealTorusCoordinates) (s : ℝ) (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun t => contourShift β s (i.insertNth t q)) (Pi.single i 1) x := by
  apply hasDerivAt_pi.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, hj⟩
  · subst j
    simpa [contourShift, complexifyCoordinates] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (s • (Complex.I * (β i : ℂ)))
  · subst j
    simpa [contourShift, complexifyCoordinates] using
      hasDerivAt_const x ((q k : ℂ) + s • (Complex.I * (β (i.succAbove k) : ℂ)))

theorem hasDerivAt_analytic_coordinate
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (s : ℝ) (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ)
    (hφ : AnalyticAt ℂ φ (contourShift β s (i.insertNth x q))) :
    HasDerivAt (fun t => φ (contourShift β s (i.insertNth t q)))
      (contourSpatialFlux φ β s i (i.insertNth x q)) x := by
  exact (hφ.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x
    (hasDerivAt_contour_coordinate β s i q x)

theorem insertNth_mem_torusCube
    {a p : ℝ} {q : Fin 2 → ℝ} (hq : ∀ j, q j ∈ Icc a (a + p))
    (i : Fin 3) {x : ℝ} (hx : x ∈ Icc a (a + p)) :
    i.insertNth x q ∈ torusCube a p := by
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using hx
  · simpa only [Fin.insertNth_apply_succAbove] using hq k

theorem contourShift_coordinate_period
    (β : RealTorusCoordinates) (s a p : ℝ) (i : Fin 3) (q : Fin 2 → ℝ) :
    contourShift β s (i.insertNth (a + p) q) =
      contourShift β s (i.insertNth a q) + (p : ℂ) • Pi.single i 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [contourShift, complexifyCoordinates, add_assoc, add_comm, add_left_comm]
  · simp [contourShift, complexifyCoordinates]

/-- The Cauchy--Riemann relation for a simultaneous imaginary translation. -/
theorem contourParameterDerivative_eq_sum_flux
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (s : ℝ) (q : RealTorusCoordinates) :
    contourParameterDerivative φ β s q =
      ∑ i, (Complex.I * (β i : ℂ)) * contourSpatialFlux φ β s i q := by
  unfold contourParameterDerivative contourSpatialFlux
  conv_lhs => arg 2; rw [pi_eq_sum_univ' (Complex.I • complexifyCoordinates β)]
  simp only [map_sum, map_smul, Pi.smul_apply, smul_eq_mul, complexifyCoordinates]

/-- Periodicity cancels the actual holomorphic coordinate flux. -/
theorem integral_analytic_spatialFlux_eq_zero
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (a p s : ℝ) (hp : 0 ≤ p) (i : Fin 3)
    (hφ : ∀ q ∈ torusCube a p, AnalyticAt ℂ φ (contourShift β s q))
    (hperiod : ∀ z : ComplexTorusCoordinates,
      φ (z + (p : ℂ) • Pi.single i 1) = φ z) :
    (∫ q, contourSpatialFlux φ β s i q ∂torusCubeMeasure a p) = 0 := by
  apply periodic_pi_flux_integral_eq_zero_ae i hp
    (f := fun q => φ (contourShift β s q))
  · filter_upwards [ae_pi_interval_mem_closed_cube 2 a p] with q hq
    intro x hx
    have hx' : x ∈ Icc a (a + p) := by
      simpa only [uIcc_of_le (le_add_of_nonneg_right hp)] using hx
    exact hasDerivAt_analytic_coordinate φ β s i q x
      (hφ _ (insertNth_mem_torusCube hq i hx'))
  · exact integrable_contourSpatialFlux φ β a p s i hφ
  · exact Filter.Eventually.of_forall fun q => by
      rw [contourShift_coordinate_period, hperiod]

/-- An analytic periodic integrand has the same integral over the real cube
and its simultaneous imaginary translate. All derivative, domination and
flux-cancellation statements are proved from the analytic tube hypothesis. -/
theorem integral_analytic_periodic_contour_invariant
    (φ : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (a p : ℝ) (hp : 0 ≤ p)
    (hφ : AnalyticOnNhd ℂ φ (contourTube β a p))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      φ (z + (p : ℂ) • Pi.single i 1) = φ z) :
    (∫ q, φ (complexifyCoordinates q + Complex.I • complexifyCoordinates β)
      ∂torusCubeMeasure a p) =
      ∫ q, φ (complexifyCoordinates q) ∂torusCubeMeasure a p := by
  have hslice : ∀ s ∈ uIcc (0 : ℝ) 1, ∀ q ∈ torusCube a p,
      AnalyticAt ℂ φ (contourShift β s q) := by
    intro s hs q hq
    apply hφ
    exact ⟨(s, q), ⟨by simpa using hs, hq⟩, rfl⟩
  have hlocal := fun s hs => analytic_contour_local_data (isCompact_torusCube a p)
    (ae_mem_torusCube a p) φ β s (hslice s hs)
  have hzero : ∀ s ∈ uIcc (0 : ℝ) 1,
      (∫ q, contourParameterDerivative φ β s q ∂torusCubeMeasure a p) = 0 := by
    intro s hs
    simp_rw [contourParameterDerivative_eq_sum_flux]
    exact integral_sum_flux_eq_zero (fun i => Complex.I * (β i : ℂ))
      (contourSpatialFlux φ β s)
      (fun i => integrable_contourSpatialFlux φ β a p s i (hslice s hs))
      (fun i => integral_analytic_spatialFlux_eq_zero φ β a p s hp i
        (hslice s hs) (hperiod i))
  have h := contour_integral_invariant (fun s q => φ (contourShift β s q))
    (contourParameterDerivative φ β) hlocal hzero
  simpa only [contourShift, one_smul, zero_smul, add_zero] using h

end Maxwell.Green
