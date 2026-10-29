import Maxwell.Green.ComplexCoercivity
import Maxwell.Green.TorusConstruction

/-! Global inverse-square control from the actual local resolvent pole and
the regular part of the compact torus. -/

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped Topology
open scoped ComplexConjugate

namespace Maxwell.Green

/-- Local spectral control and a far-region bound glue to the actual
three-dimensional integrable majorant. This applies to scalar or matrix
resolvent components. -/
theorem localPole_far_bound_majorant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H A B : RealTorusCoordinates → V) (z : RealTorusCoordinates → ℂ)
    (U : Set RealTorusCoordinates) (CA CB CD CF a p : ℝ)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCD : 0 ≤ CD) (hCF : 0 ≤ CF)
    (hlocal : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 → H q = (z q)⁻¹ • A q + B q)
    (hA : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 → ‖A q‖ ≤ CA)
    (hB : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 → ‖B q‖ ≤ CB)
    (hz : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
      ‖(z q)⁻¹‖ ≤ CD * inverseSquare (toLp 2 q))
    (hfar : ∀ q ∈ torusCube a p, q ∉ U → ‖H q‖ ≤ CF) :
    ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant (CA * CD + CB + CF) q := by
  intro q hq hq₀
  have hs := inverseSquare_nonneg (toLp 2 q)
  have hC : 0 ≤ CA * CD + CB := add_nonneg (mul_nonneg hCA hCD) hCB
  by_cases hU : q ∈ U
  · rw [hlocal q hq hU hq₀]
    calc
      ‖(z q)⁻¹ • A q + B q‖ ≤ ‖(z q)⁻¹ • A q‖ + ‖B q‖ := norm_add_le _ _
      _ = ‖(z q)⁻¹‖ * ‖A q‖ + ‖B q‖ := by rw [norm_smul]
      _ ≤ (CD * inverseSquare (toLp 2 q)) * CA + CB :=
        add_le_add (mul_le_mul (hz q hq hU hq₀) (hA q hq hU hq₀)
          (norm_nonneg _) (mul_nonneg hCD hs)) (hB q hq hU hq₀)
      _ ≤ (CA * CD + CB) * (1 + inverseSquare (toLp 2 q)) := by
        nlinarith [mul_nonneg hCA hCD, mul_nonneg hCB hs]
      _ ≤ coordinateBoundaryMajorant (CA * CD + CB + CF) q := by
        unfold coordinateBoundaryMajorant boundaryMajorant
        exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · have hfarq := hfar q hq hU
    unfold coordinateBoundaryMajorant boundaryMajorant
    nlinarith [mul_nonneg (add_nonneg hC hCF) hs]

/-- Continuity on the compact local chart and the compact far region
supplies all numerator, regular-part, and far-region constants. Only the
local inverse denominator estimate remains as a spectral input. -/
theorem exists_majorant_of_compact_localPole
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H A B : RealTorusCoordinates → V) (z : RealTorusCoordinates → ℂ)
    (U K : Set RealTorusCoordinates) (a p CD : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K) (hCD : 0 ≤ CD)
    (hA : ContinuousOn A K) (hB : ContinuousOn B K)
    (hfar : ContinuousOn H (torusCube a p \ U))
    (hlocal : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 → H q = (z q)⁻¹ • A q + B q)
    (hz : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
      ‖(z q)⁻¹‖ ≤ CD * inverseSquare (toLp 2 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q := by
  obtain ⟨CA, hCA⟩ := hK.exists_bound_of_continuousOn hA
  obtain ⟨CB, hCB⟩ := hK.exists_bound_of_continuousOn hB
  obtain ⟨CF, hCF⟩ := ((isCompact_torusCube a p).diff hU).exists_bound_of_continuousOn hfar
  refine ⟨max CA 0 * CD + max CB 0 + max CF 0, by positivity, ?_⟩
  apply localPole_far_bound_majorant H A B z U (max CA 0) (max CB 0) CD (max CF 0) a p
    (le_max_right _ _) (le_max_right _ _) hCD (le_max_right _ _) hlocal
  · intro q _ hq _
    exact (hCA q (hUK hq)).trans (le_max_left _ _)
  · intro q _ hq _
    exact (hCB q (hUK hq)).trans (le_max_left _ _)
  · exact hz
  · intro q hq hqU
    exact (hCF q ⟨hq, hqU⟩).trans (le_max_left _ _)

/-- The compact local pole construction also proves integrability of the
original scalar boundary amplitude; measurability is obtained from ordinary
continuity away from its single singular point. -/
theorem integrable_of_compact_localPole
    (H A B : RealTorusCoordinates → ℂ) (z : RealTorusCoordinates → ℂ)
    (U K : Set RealTorusCoordinates) (a p CD : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K) (hzero : (0 : RealTorusCoordinates) ∈ U)
    (hCD : 0 ≤ CD) (hA : ContinuousOn A K) (hB : ContinuousOn B K)
    (hH : ∀ q ∈ torusCube a p, q ≠ 0 → ContinuousAt H q)
    (hlocal : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 → H q = (z q)⁻¹ • A q + B q)
    (hz : ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
      ‖(z q)⁻¹‖ ≤ CD * inverseSquare (toLp 2 q)) :
    Integrable H (torusCubeMeasure a p) := by
  have hfar : ContinuousOn H (torusCube a p \ U) := by
    intro q hq
    exact (hH q hq.1 (fun h => hq.2 (h ▸ hzero))).continuousWithinAt
  obtain ⟨C, _, hb⟩ := exists_majorant_of_compact_localPole H A B z U K a p CD
    hU hK hUK hCD hA hB hfar hlocal hz
  exact integrable_of_punctured_cube_inverseSquare H C a p hH hb

/-- Analyticity, positive real Hessian and the actual reflection symmetry
supply the local reciprocal estimate in the global resolvent majorant.
The local pole identity and ordinary compact-region continuity are the only
remaining amplitude hypotheses. -/
theorem analytic_resolvent_majorant
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : RealTorusCoordinates), ‖β‖ < δ → ∀ E : ℝ,
      E ≤ (lam (Complex.I • complexifyCoordinates β)).re →
      ∀ (H A B : RealTorusCoordinates → ℂ) (U K : Set RealTorusCoordinates) (a p : ℝ),
      IsOpen U → IsCompact K → U ⊆ K →
      (∀ q ∈ U, ‖toLp 2 q‖ < δ) →
      ContinuousOn A K → ContinuousOn B K → ContinuousOn H (torusCube a p \ U) →
      (∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
        H q = (lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ))⁻¹ *
          A q + B q) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ torusCube a p, q ≠ 0 →
        ‖H q‖ ≤ coordinateBoundaryMajorant C q := by
  obtain ⟨δ, CD, hδ, hCD, hden⟩ := analytic_edge_inverseSquare_bound lam hlam hpos hsym
  refine ⟨δ, hδ, ?_⟩
  intro β hβ E hE H A B U K a p hU hK hUK hsmall hA hB hfar hlocal
  apply exists_majorant_of_compact_localPole H A B
    (fun q => lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ))
    U K a p CD hU hK hUK hCD.le hA hB hfar hlocal
  intro q _ hq hq₀
  have he : toLp 2 q ≠ (0 : Momentum) := by
    intro hzero
    exact hq₀ (congrArg WithLp.ofLp hzero)
  exact hden (toLp 2 q) β (hsmall q hq) hβ he E hE

/-- Away from a boundary pole, ordinary continuity gives the actual limit
of the shifted contour density. -/
theorem tendsto_contourShift_value
    {V : Type*} [TopologicalSpace V]
    (φ : ComplexTorusCoordinates → V) (β q : RealTorusCoordinates)
    (hφ : ContinuousAt φ (contourShift β 1 q)) :
    Tendsto (fun t => φ (contourShift β t q)) (𝓝[<] (1 : ℝ))
      (𝓝 (φ (contourShift β 1 q))) := by
  have hc : ContinuousAt (fun t : ℝ => contourShift β t q) 1 :=
    (continuous_contourShift β).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  exact (hφ.tendsto.comp hc.tendsto).mono_left nhdsWithin_le_nhds

end Maxwell.Green
