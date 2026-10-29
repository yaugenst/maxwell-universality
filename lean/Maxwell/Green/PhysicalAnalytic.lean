import Maxwell.Green.BlockIntegral
import Maxwell.Green.BlockContour
import Maxwell.Spectral.ConventionalAnalytic
import Maxwell.Spectral.ComplexContourGap

/-! The analytic Green density is the continuation of the exact physical
weighted block integral, with the same lattice source and scalar material. -/
namespace Maxwell.Green.PhysicalAnalytic

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.SourceProfile Maxwell.Green.PhysicalCompression
open MeasureTheory
noncomputable section
variable {N : ℕ}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The genuine shifted conventional-cell operator family. -/
def shiftedOperator (material : Cell20 → ℝ) (E : ℝ) (z : ComplexTorusCoordinates) :
    EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20 :=
  ConventionalAnalytic.operator material z - (E : ℂ) • 1

def density (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (z : ComplexTorusCoordinates) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (sourceLeft edges W z).comp ((shiftedOperator material E z).inverse.comp (sourceRight edges W z))

theorem shiftedOperator_analyticAt (material : Cell20 → ℝ) (E : ℝ)
    (z : ComplexTorusCoordinates) : AnalyticAt ℂ (shiftedOperator material E) z :=
  (ConventionalAnalytic.operator_analyticAt material z).sub analyticAt_const

theorem density_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (z : ComplexTorusCoordinates)
    (hz : (shiftedOperator material E z).IsInvertible) :
    AnalyticAt ℂ (density edges W material E) z :=
  Defect.analyticAt_operator_composition (sourceLeft edges W)
    (fun w => (shiftedOperator material E w).inverse.comp (sourceRight edges W w)) z
    (sourceLeft_analyticAt edges W z)
    (Defect.analyticAt_operator_composition (fun w => (shiftedOperator material E w).inverse)
      (sourceRight edges W) z
      (ComplexContourGap.analyticAt_inverse_family (shiftedOperator_analyticAt material E z) hz)
      (sourceRight_analyticAt edges W z))

theorem shiftedOperator_real (material : Cell20 → ℝ) (E : ℝ) (q : RealTorusCoordinates) :
    shiftedOperator material E (complexifyCoordinates q) =
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric (PeriodicYee.edgeAverage material) (angularTorusPoint q) - (E : ℂ) • 1) := by
  have hq : complexifyCoordinates q = ConventionalAnalytic.realMomentum q := rfl
  have ht : angularTorusPoint q = Maxwell.Spectral.Bloch.momentumTorus q := rfl
  rw [shiftedOperator, hq, ConventionalAnalytic.operator_real, ht,
    torusElectric_eq_periodic]
  simp only [map_sub, map_smul, map_one]

theorem density_real (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (q : RealTorusCoordinates) :
    density edges W material E (complexifyCoordinates q) =
      torusBlock edges W (PeriodicYee.edgeAverage material) E (angularTorusPoint q) := by
  rw [torusBlock_angular edges W _ E hE, density, shiftedOperator_real]
  rfl

theorem phase_periodic (n : Site) (i : Fin 3) (z : ComplexTorusCoordinates) :
    phase n (z + (2 * Real.pi : ℂ) • Pi.single i 1) = phase n z := by
  have he : phase n = complexFourierFactor n := by
    funext w
    simp only [phase, complexFourierFactor, complexIntegerPairing_apply]
  rw [he]
  exact complexFourierFactor_periodic n i z

theorem sourceRight_periodic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (i : Fin 3) (z : ComplexTorusCoordinates) :
    sourceRight edges W (z + (2 * Real.pi : ℂ) • Pi.single i 1) = sourceRight edges W z := by
  unfold sourceRight
  congr 1
  ext r j
  simp only [rightMatrix, phase_periodic]

theorem sourceLeft_periodic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (i : Fin 3) (z : ComplexTorusCoordinates) :
    sourceLeft edges W (z + (2 * Real.pi : ℂ) • Pi.single i 1) = sourceLeft edges W z := by
  unfold sourceLeft
  congr 1
  ext r j
  simp only [leftMatrix, phase_periodic]

theorem boundaryPhase_eq_phase (z : ComplexTorusCoordinates) (j : Fin 3) (r : Cell20) :
    ConventionalAnalytic.boundaryPhase z j r =
      if r j = 19 then phase (unitSite j) z else 1 := by
  simp only [ConventionalAnalytic.boundaryPhase, phase, unitSite]
  congr 2
  simp [Pi.single_apply]

theorem curl_periodic (i : Fin 3) (z : ComplexTorusCoordinates) :
    ConventionalAnalytic.curl (z + (2 * Real.pi : ℂ) • Pi.single i 1) =
      ConventionalAnalytic.curl z := by
  ext r s
  simp only [ConventionalAnalytic.curl, ConventionalAnalytic.difference,
    boundaryPhase_eq_phase, phase_periodic]

theorem operator_periodic (material : Cell20 → ℝ) (i : Fin 3) (z : ComplexTorusCoordinates) :
    ConventionalAnalytic.operator material (z + (2 * Real.pi : ℂ) • Pi.single i 1) =
      ConventionalAnalytic.operator material z := by
  have hn : ConventionalAnalytic.curl (-(z + (2 * Real.pi : ℂ) • Pi.single i 1)) =
      ConventionalAnalytic.curl (-z) := by
    have h := curl_periodic i (-z - (2 * Real.pi : ℂ) • Pi.single i 1)
    rw [sub_add_cancel] at h
    convert h.symm using 1
    congr 1
    abel
  unfold ConventionalAnalytic.operator ConventionalAnalytic.fiber ConventionalAnalytic.formalAdjointCurl
  rw [curl_periodic, hn]

theorem density_periodic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (i : Fin 3) (z : ComplexTorusCoordinates) :
    density edges W material E (z + (2 * Real.pi : ℂ) • Pi.single i 1) =
      density edges W material E z := by
  unfold density shiftedOperator
  rw [sourceLeft_periodic, sourceRight_periodic, operator_periodic]

/-- Exact density identity for the actual infinite weighted block. -/
theorem weightedBlock_density_integral (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (v : Site) (d : ℕ) :
    weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material)) K hK hm -
        (E : ℂ) • 1)) (fun i => (d : ℤ) * v i) =
      (1 / (2 * Real.pi)^3 : ℝ) •
        ∫ q, torusFourierFactor d v q • density edges W material E (complexifyCoordinates q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [weightedBlock_eq_angular_integral edges W _ K hK hm E hE]
  simp only [density_real edges W material E hE]

end
end Maxwell.Green.PhysicalAnalytic
