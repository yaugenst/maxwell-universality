import Maxwell.Composition.ConventionalPlatform
import Maxwell.Defect.WeightedModeRefinement

/-! Retain the accepted finite certificate and its executable refinement
alongside the physical platform, with exact same-mode correspondence. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Defect.ScalarDefect Maxwell.Green
open Maxwell.Certificate Maxwell.Certificate.PointWitness

structure SelectedPlatform where
  spectral : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum
  certificate : ConventionalCertifiedCube spectral
  physical : PhysicalPlatform
  defect_eq : physical.defect = ScalarDefect.cube certificate.size
  material_eq : physical.background.material = operatingMaterial (dyadicCandidate certificate.index)
  placement_eq : physical.basis = certificate.placement
  eigenvalue_eq : physical.eigenvalue = certificate.eigenvalue
  mode_eq : HEq physical.mode certificate.mode
  rowBound_eq : physical.rowBound = 16
  bulkGap_eq : physical.bulkGap = certificate.gap
  coreFloor : ∃ Q : PhysicalPlatform, physical = Q.withCoreFloor

theorem exists_selected_platform (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) (hglobal : PointRealEdgeExclusion) :
    Nonempty SelectedPlatform := by
  obtain ⟨S, C, P, hD, hm, hB, hμ, hu, hrow, hgap', hfloor⟩ :=
    exists_conventional_physical_platform hgap hexclude hglobal
  exact ⟨⟨S, C, P, hD, hm, hB, hμ, hu, hrow, hgap', hfloor⟩⟩

namespace SelectedPlatform

def certificateApproximation (P : SelectedPlatform) (b : ℕ) :
    Fin (ScalarDefect.edges (ScalarDefect.cube P.certificate.size)).card → ℚ :=
  P.certificate.refinementPlan.approximation
    (scalarBinaryCompression (ScalarDefect.cube P.certificate.size)
      FiniteStencil.frozenEdgeCoefficientQ (dyadicCandidate P.certificate.index)
      P.certificate.normBound P.certificate.gap P.certificate.gap_pos
      P.certificate.normBound_pos P.certificate.gap_le)
    (1 + 2 * P.certificate.gap⁻¹) b

def modeApproximation (P : SelectedPlatform) (b : ℕ) :
    Fin (ScalarDefect.edges P.physical.defect).card → ℚ :=
  P.defect_eq.symm ▸ P.certificateApproximation b

theorem transport_approximation {D D' : Finset Site} (h : D = D')
    (u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (v : EuclideanSpace ℝ (Fin (ScalarDefect.edges D').card)) (hu : HEq u v)
    (q : Fin (ScalarDefect.edges D').card → ℚ) (ε : ℝ)
    (hq : ‖rationalVector q‖ ≤ 1 ∧ ‖rationalVector q-v‖ ≤ ε) :
    ‖rationalVector (h.symm ▸ q)‖ ≤ 1 ∧ ‖rationalVector (h.symm ▸ q)-u‖ ≤ ε := by
  cases h
  have hv : u = v := eq_of_heq hu
  simpa only [hv] using hq

theorem modeApproximation_spec (P : SelectedPlatform) (b : ℕ) :
    ‖rationalVector (P.modeApproximation b)‖ ≤ 1 ∧
    ‖rationalVector (P.modeApproximation b)-P.physical.mode‖ ≤ (1/2 : ℝ)^b :=
  transport_approximation P.defect_eq P.physical.mode P.certificate.mode P.mode_eq
    (P.certificateApproximation b) _ (P.certificate.refinement_error b)

def weightedApproximation (P : SelectedPlatform) (b : ℕ) :
    Fin (ScalarDefect.edges P.physical.defect).card → ℚ :=
  WeightedModeRefinement.weightedVector (ScalarDefect.coordinateWeight P.physical.defect)
    P.modeApproximation b

theorem weightedApproximation_spec (P : SelectedPlatform) (b : ℕ) :
    ‖rationalVector (P.weightedApproximation b)‖ ≤ 1 ∧
    ‖rationalVector (P.weightedApproximation b)-P.physical.weightedMode‖ ≤ (1/2 : ℝ)^b := by
  have hh := WeightedModeRefinement.weightedVector_spec
    (ScalarDefect.coordinateWeight P.physical.defect) P.modeApproximation P.physical.mode
    (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds P.physical.defect i).1)
    (fun i => (ScalarDefect.coordinateWeight_bounds P.physical.defect i).2)
    P.physical.mode_unit (fun p => (P.modeApproximation_spec p).1)
    (fun p => by simpa only [one_div, inv_pow] using (P.modeApproximation_spec p).2) b
  simpa only [weightedApproximation, PhysicalPlatform.weightedMode, one_div, inv_pow] using hh

end SelectedPlatform
end Maxwell.Composition
