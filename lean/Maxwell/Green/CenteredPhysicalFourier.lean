import Maxwell.Green.PhysicalLower
import Maxwell.Green.BoundaryFourier

/-! The centered real Bloch integral and the singular contour formula for
the actual weighted lattice block, including the phase of a nonzero edge
momentum. -/

noncomputable section

namespace Maxwell.Green

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open SourceProfile PhysicalCompression PhysicalAnalytic PhysicalLower
open MeasureTheory Set
open scoped Topology InnerProductSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

@[simp] theorem angularTorusPoint_add (q r : RealTorusCoordinates) :
    angularTorusPoint (q + r) = angularTorusPoint q + angularTorusPoint r := by
  ext i
  simp [angularTorusPoint, add_div]

theorem torusFourierFactor_add (d : ℕ) (v : Fin 3 → ℤ)
    (q r : RealTorusCoordinates) :
    torusFourierFactor d v (q + r) =
      torusFourierFactor d v q * torusFourierFactor d v r := by
  unfold torusFourierFactor oscillatoryFactor
  rw [map_add, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem scalarDensity_real_centered {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (E : ℝ) (u : EuclideanSpace ℂ (Fin N)) (θ q : RealTorusCoordinates)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t)) :
    scalarDensity edges W material E u θ (complexifyCoordinates q) =
      scalarOperatorReadout u
        (torusBlock edges W (PeriodicYee.edgeAverage material) E
          (angularTorusPoint θ + angularTorusPoint q)) := by
  unfold scalarDensity
  have he : complexifyCoordinates θ + complexifyCoordinates q =
      complexifyCoordinates (θ + q) := by
    ext i
    simp [complexifyCoordinates]
  rw [he, density_real edges W material E hE, angularTorusPoint_add]

/-- Centering normalized Haar measure gives the actual scalar block as the
real Fourier coefficient of the centered analytic density. -/
theorem weightedBlock_centered_scalar_integral {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K)
    (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (v : Site) (d : ℕ) :
    inner ℂ u (weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
        K hK hm - (E : ℂ) • 1)) (fun i => (d : ℤ) * v i) u) =
      torusFourierFactor d v θ *
        (((2 * Real.pi : ℂ) ^ 3)⁻¹ *
          ∫ q, torusFourierFactor d v q *
            scalarDensity edges W material E u θ (complexifyCoordinates q)
            ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
  let f : Torus → ℂ := fun t => UnitAddTorus.mFourier (fun i => (d : ℤ) * v i) t *
    scalarOperatorReadout u (torusBlock edges W (PeriodicYee.edgeAverage material) E t)
  have hc : Continuous f :=
    (UnitAddTorus.mFourier _).continuous.mul
      ((scalarOperatorReadout u).continuous.comp (torusBlock_continuous edges W _ E))
  have hi : inner ℂ u (weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
        K hK hm - (E : ℂ) • 1)) (fun i => (d : ℤ) * v i) u) = ∫ t, f t := by
    rw [weightedBlock_integral edges W u _ K hK hm E hE]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [f, torusBlock_readout edges W _ E hE]
  rw [hi]
  have hhaar : (volume : Measure Torus) = Maxwell.Defect.TorusChart.haar := rfl
  rw [hhaar, integral_centered_angularTorus_complex f hc.aestronglyMeasurable
    (angularTorusPoint θ)]
  have hf (q : RealTorusCoordinates) : f (angularTorusPoint θ + angularTorusPoint q) =
      torusFourierFactor d v θ *
        (torusFourierFactor d v q *
          scalarDensity edges W material E u θ (complexifyCoordinates q)) := by
    simp only [f, ← angularTorusPoint_add, mFourier_angularTorusPoint_direction,
      torusFourierFactor_add, scalarDensity_real_centered edges W material E u θ q hE]
    rw [angularTorusPoint_add]
    ring
  simp_rw [hf]
  rw [integral_const_mul]
  ring

namespace TorusLocalAssemblyData

theorem fullScalarGreen_real_phase {v : Fin 3 → ℤ} (D : TorusLocalAssemblyData v)
    (θ : RealTorusCoordinates) (σ : ℝ) (d : ℕ) :
    D.fullScalarGreen (integerPairingCLM v θ) σ d =
      torusFourierFactor d v θ * D.fullScalarGreen 0 σ d := by
  unfold fullScalarGreen scalarShiftFactor torusFourierFactor oscillatoryFactor
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end TorusLocalAssemblyData

/-- The same actual weighted lattice block equals the full scalar Green
function produced by the local saddle construction. Both the real centering
and the singular boundary shift are proved integral identities. -/
theorem weightedBlock_eq_fullScalarGreen {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K)
    (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (u : EuclideanSpace ℂ (Fin N)) (θ β : RealTorusCoordinates)
    {v : Site} (D : TorusLocalAssemblyData v)
    (hσ : 0 ≤ integerPairingCLM v β)
    (hR : ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ (scalarDensity edges W material E u θ)
      (contourTube (t • β) (-Real.pi) (2 * Real.pi)))
    (hboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ContinuousAt (scalarDensity edges W material E u θ) (contourShift β 1 q))
    (C : ℝ)
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖scalarDensity edges W material E u θ (contourShift β t q)‖ ≤
        coordinateBoundaryMajorant C q)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      D.H q = scalarDensity edges W material E u θ (contourShift β 1 q))
    (d : ℕ) :
    inner ℂ u (weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
        K hK hm - (E : ℂ) • 1)) (fun i => (d : ℤ) * v i) u) =
      D.fullScalarGreen (integerPairingCLM v θ) (integerPairingCLM v β) d := by
  rw [weightedBlock_centered_scalar_integral edges W material K hK hm E hE u θ v d,
    D.fullScalarGreen_real_phase θ]
  congr 1
  exact (D.fullScalarGreen_eq_real_fourier (scalarDensity edges W material E u θ) β
    hσ hR (scalarDensity_periodic edges W material E u θ) hboundary C hbound hH d).symm

end Maxwell.Green
