import Maxwell.Composition.OperatingPlatform
import Maxwell.Composition.PhysicalFloor
import Maxwell.Defect.ConventionalCertifiedDefect

/-! The same accepted scalar-defect certificate supplies the fixed physical
platform. The selected record is retained so its executable refinement plan
remains tied to the actual mode used in every Green bound. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Defect.ScalarDefect Maxwell.Green Maxwell.Green.PhysicalAnalytic
open Maxwell.Certificate Maxwell.Certificate.PointWitness
set_option maxHeartbeats 1200000

theorem cube_nonempty (L : ℕ) : (ScalarDefect.cube L).Nonempty := by
  refine ⟨0, (mem_cube L 0).mpr ?_⟩
  intro j
  simp only [Pi.zero_apply]
  constructor <;> omega

theorem selected_cube_has_physical_platform
    {S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum}
    (C : ConventionalCertifiedCube S) :
    ∃ P : PhysicalPlatform,
      P.defect = ScalarDefect.cube C.size ∧
      P.background.material = operatingMaterial (dyadicCandidate C.index) ∧
      P.basis = C.placement ∧ P.eigenvalue = C.eigenvalue ∧ HEq P.mode C.mode ∧
      P.rowBound = 16 ∧ P.bulkGap = C.gap ∧
      ∃ Q : PhysicalPlatform, P = Q.withCoreFloor := by
  obtain ⟨spacing, C₀, hc, hC₀, _, hfloor, hupper, hlower⟩ :=
    C.spacing (SourceDefectLayout.radius (ScalarDefect.cube C.size) + 1)
  have hz : (0 : ℚ) ≤ dyadicCandidate C.index := by
    exact_mod_cast C.energy_pos.le
  have he : physicalGreenBlock (ScalarDefect.cube C.size)
      (Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate C.index))) 0 C.mode =
        C.eigenvalue • C.mode := by
    rw [physicalGreenBlock_frozen_zero]
    exact C.mode_equation
  have hs : (physicalGreenBlock (ScalarDefect.cube C.size)
      (Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate C.index))) 0).toLinearMap.IsSymmetric := by
    rw [physicalGreenBlock_frozen_zero]
    exact FiniteStencil.weightedInverseCompression_symmetric _ _ _ _ _ _ _
  have hsimple : Module.finrank ℝ (Module.End.eigenspace
      (physicalGreenBlock (ScalarDefect.cube C.size)
        (Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate C.index))) 0).toLinearMap
          C.eigenvalue) = 1 := by
    rw [physicalGreenBlock_frozen_zero]
    exact C.mode_simple
  obtain ⟨Q, hback, hD, hB, _, _, _, hμ, hmode, hrow, hgap⟩ :=
    exists_operating_platform (dyadicCandidate C.index) hz C.energy_upper
      (ScalarDefect.cube C.size) (cube_nonempty C.size) C.operator_isUnit C.gap C.gap_pos
      C.inverse_norm C.mode C.eigenvalue C.mode_unit he hs hsimple C.eigenvalue_gt
      C.placement C.placement_isUnit spacing C₀ hC₀ hc hfloor hupper hlower
  refine ⟨Q.withCoreFloor, hD, ?_, hB, hμ, hmode, hrow, hgap, Q, rfl⟩
  change Q.background.material = operatingMaterial (dyadicCandidate C.index)
  rw [hback]
  rfl

theorem exists_conventional_physical_platform
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion)
    (hglobal : PointRealEdgeExclusion) :
    ∃ S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum,
      ∃ C : ConventionalCertifiedCube S, ∃ P : PhysicalPlatform,
        P.defect = ScalarDefect.cube C.size ∧
        P.background.material = operatingMaterial (dyadicCandidate C.index) ∧
        P.basis = C.placement ∧ P.eigenvalue = C.eigenvalue ∧ HEq P.mode C.mode ∧
        P.rowBound = 16 ∧ P.bulkGap = C.gap ∧
        ∃ Q : PhysicalPlatform, P = Q.withCoreFloor := by
  obtain ⟨S, ⟨C⟩⟩ := exists_conventional_certified_cube hgap hexclude hglobal
  exact ⟨S, C, selected_cube_has_physical_platform C⟩

end Maxwell.Composition
