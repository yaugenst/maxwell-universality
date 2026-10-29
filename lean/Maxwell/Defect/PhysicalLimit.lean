import Maxwell.Green.BlockIntegral
import Maxwell.Defect.AnalyticLocalChart
import Maxwell.Defect.RegularIntegral

/-! The local pole and the complementary/far terms of the actual finite
compression. The limiting operator is defined by convergent finite Bloch
integrals, rather than by an inverse at the spectral edge. -/
namespace Maxwell.Defect.PhysicalLimit

open MeasureTheory Set Filter Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.PhysicalCompression Maxwell.Green.SourceProfile
open Maxwell.Spectral.AnalyticEigenbranch
open scoped Topology
noncomputable section
variable {N : ℕ}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
set_option maxHeartbeats 1200000

abbrev LocalOperator := EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)
abbrev FiberOperator := EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20

def compression (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (E : ℝ) : LocalOperator (N := N) :=
  sourceCompression (defectInjection edges W)
    (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (E : ℂ) • 1))

theorem compression_eq_weightedBlock_zero (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (E : ℝ) :
    compression edges W m K hK hm E = weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (E : ℂ) • 1)) 0 := by
  have he : translatedEmbedding edges 0 = edges := by
    apply Function.Embedding.ext
    intro i
    change ((edges i).1, (edges i).2 - 20 • (0 : Site)) = edges i
    simp
  rw [weightedBlock, he]
  rfl

theorem compression_eq_integral (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric m t)) :
    compression edges W m K hK hm E = ∫ t : Torus, torusBlock edges W m E t := by
  rw [compression_eq_weightedBlock_zero, weightedBlock_eq_integral edges W m K hK hm E hE]
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]

def fiber (m : Edge20 → ℝ) (center : Torus) (q : Momentum) : FiberOperator :=
  Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
    (torusElectric m (center + TorusChart.momentumTorus q))

def localSource (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (center : Torus) (q : Momentum) :=
  torusSource edges W (center + TorusChart.momentumTorus q)

def numerator (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (center : Torus)
    (P : Momentum → FiberOperator) (q : Momentum) : LocalOperator (N := N) :=
  sourceCompression (localSource edges W center q) (P q)

/-- Pointwise inverse, also defined on the far region at the edge energy.
The inverse in the algebra of continuous symbols is unavailable at that energy. -/
def fullDensity (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (m : Edge20 → ℝ)
    (center : Torus) (E : ℝ) (q : Momentum) : LocalOperator (N := N) :=
  sourceCompression (localSource edges W center q) ((fiber m center q) - (E : ℂ) • 1).inverse

def regularDensity (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (m : Edge20 → ℝ)
    (center : Torus) (P : Momentum → FiberOperator) (edge ξ : ℝ) (q : Momentum) :
    LocalOperator (N := N) :=
  sourceCompression (localSource edges W center q)
    (regularResolvent (fiber m center q) (P q) (edge - ξ))

def regularPart (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (m : Edge20 → ℝ)
    (center : Torus) (P : Momentum → FiberOperator) (edge radius ξ : ℝ) :
    LocalOperator (N := N) :=
  (∫ q in Metric.ball 0 radius, regularDensity edges W m center P edge ξ q) +
    ∫ q in TorusChart.physicalCell \ Metric.ball 0 radius,
      fullDensity edges W m center (edge - ξ) q

theorem torusBlock_eq_compression (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric m t))
    (center : Torus) (q : Momentum) :
    torusBlock edges W m E (center + TorusChart.momentumTorus q) =
      sourceCompression (localSource edges W center q)
        ((fiber m center q) - (E : ℂ) • 1).inverse := by
  unfold torusBlock
  rw [Maxwell.Spectral.BlochResolvent.inverseElectricSymbol_apply m E hE,
    matrixInverse_operator]
  simp only [map_sub, map_smul, map_one]
  rfl

/-- Pointwise pole extraction for the actual physical finite-source block. -/
theorem torusBlock_pole (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (m : Edge20 → ℝ)
    (center : Torus) (P : Momentum → FiberOperator) (d : Momentum → ℝ)
    (edge ξ : ℝ) (q : Momentum)
    (hE : ∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric m t))
    (hPP : P q * P q = P q)
    (hTP : fiber m center q * P q = ((edge + d q : ℝ) : ℂ) • P q)
    (hPT : P q * fiber m center q = ((edge + d q : ℝ) : ℂ) • P q)
    (hi : (fiber m center q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible)
    (hne : d q + ξ ≠ 0) :
    torusBlock edges W m (edge - ξ) (center + TorusChart.momentumTorus q) =
      (d q + ξ)⁻¹ • numerator edges W center P q + regularDensity edges W m center P edge ξ q := by
  have he : ((edge + d q : ℝ) : ℂ) - ((edge - ξ : ℝ) : ℂ) = ((d q + ξ : ℝ) : ℂ) := by
    push_cast
    ring
  have hp := (inverse_eq_pole_add_regular (fiber m center q) (P q)
    ((edge + d q : ℝ) : ℂ) ((edge - ξ : ℝ) : ℂ) hPP hTP hPT hi
    (by rw [he]; exact Complex.ofReal_ne_zero.mpr hne)).2
  rw [torusBlock_eq_compression edges W m (edge - ξ) hE center q,
    sourceCompression_pole_decomposition _ _ _ _ _ _ hp, he]
  congr 1
  · apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [numerator, Complex.real_smul]
  · simp only [regularDensity, Complex.ofReal_sub]

/-- Splitting normalized Haar measure and extracting the local pole gives
the actual compression, with an explicitly defined regular/far remainder. -/
theorem compression_decomposition (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (d : Momentum → ℝ)
    (edge ξ : ℝ) (C : LocalBandChart (LocalOperator (N := N)))
    (hr : C.radius ≤ Real.pi)
    (hE : ∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric m t))
    (hpole : ∀ q ∈ Metric.ball 0 C.radius,
      torusBlock edges W m (edge - ξ) (center + TorusChart.momentumTorus q) =
        (d q + ξ)⁻¹ • numerator edges W center P q + regularDensity edges W m center P edge ξ q)
    (hchart : C.localPart ξ = ∫ q in Metric.ball 0 C.radius,
      (d q + ξ)⁻¹ • numerator edges W center P q)
    (hnum : IntegrableOn (fun q => (d q + ξ)⁻¹ • numerator edges W center P q)
      (Metric.ball 0 C.radius))
    (hreg : IntegrableOn (regularDensity edges W m center P edge ξ) (Metric.ball 0 C.radius)) :
    compression edges W m K hK hm (edge - ξ) =
      (1 / (2 * Real.pi)^3 : ℝ) •
        (C.localPart ξ + regularPart edges W m center P edge C.radius ξ) := by
  have hi : Integrable (torusBlock edges W m (edge - ξ)) TorusChart.haar := by
    have hhaar : (volume : Measure Torus) = TorusChart.haar := rfl
    rw [← hhaar]
    exact (torusBlock_continuous edges W m (edge - ξ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [compression_eq_integral edges W m K hK hm (edge - ξ) hE]
  have hhaar : (volume : Measure Torus) = TorusChart.haar := rfl
  rw [hhaar, TorusChart.integral_local_far _ hi center hr]
  have hp : (∫ q in Metric.ball 0 C.radius,
      torusBlock edges W m (edge - ξ) (center + TorusChart.momentumTorus q)) =
      C.localPart ξ + ∫ q in Metric.ball 0 C.radius, regularDensity edges W m center P edge ξ q := by
    rw [hchart, ← integral_add hnum hreg]
    exact setIntegral_congr_fun measurableSet_ball hpole
  rw [hp, regularPart, add_assoc]
  congr 2
  congr 1
  apply setIntegral_congr_fun (TorusChart.measurableSet_physicalCell.diff measurableSet_ball)
  intro q _
  exact torusBlock_eq_compression edges W m (edge - ξ) hE center q

def edgeLimit (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (m : Edge20 → ℝ)
    (center : Torus) (P : Momentum → FiberOperator) (edge : ℝ)
    (C : LocalBandChart (LocalOperator (N := N))) : LocalOperator (N := N) :=
  (1 / (2 * Real.pi)^3 : ℝ) •
    (C.localPart 0 + regularPart edges W m center P edge C.radius 0)

end
end Maxwell.Defect.PhysicalLimit
