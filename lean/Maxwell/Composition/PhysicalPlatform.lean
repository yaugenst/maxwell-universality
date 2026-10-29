import Maxwell.Composition.DecoratedGram
import Maxwell.Composition.SourceRecovery
import Maxwell.Realization.PhysicalRates
import Maxwell.Realization.Parameters

/-! Fixed analytic data of the actual scalar-cell platform. Every operator
is tied to the same periodic material and the same finite scalar defect.
Input-dependent calibration algorithms are deliberately separate. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open scoped InnerProduct

/-- Rational operating material, after folding the selected rational
spectral shift into its scalar cells. The reserve is in scalar-cell units. -/
structure PeriodicScalarBackground where
  material : Cell20 → ℚ
  reserve : ℚ
  reserve_pos : 0 < reserve
  bounds : ∀ c, 1 ≤ material c ∧ material c ≤ 25 - reserve

namespace PeriodicScalarBackground

def scalar (P : PeriodicScalarBackground) (c : Site) : ℝ := P.material (siteMod20 c)

def edgeMaterial (P : PeriodicScalarBackground) : Edge20 → ℝ :=
  PeriodicYee.edgeAverage (fun c => (P.material c : ℝ))

theorem material_bounds (P : PeriodicScalarBackground) (c : Cell20) :
    (1 : ℝ) ≤ P.material c ∧ (P.material c : ℝ) ≤ 25 := by
  have hc := P.bounds c
  have hr := P.reserve_pos
  have hu : P.material c ≤ (25 : ℚ) := by linarith
  exact ⟨by exact_mod_cast hc.1, by exact_mod_cast hu⟩

theorem edge_bound (P : PeriodicScalarBackground) (e : Edge) :
    |periodicCoefficient P.edgeMaterial e| ≤ 25 := by
  have h := PeriodicYee.edgeAverage_bounds (fun c => (P.material c : ℝ)) 1 25 P.material_bounds (edgeMod20 e)
  change |PeriodicYee.edgeAverage (fun c => (P.material c : ℝ)) (edgeMod20 e)| ≤ 25
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩

def operator (P : PeriodicScalarBackground) : Field →L[ℂ] Field :=
  electricOperator (periodicCoefficient P.edgeMaterial) 25 (by norm_num) P.edge_bound

end PeriodicScalarBackground

def physicalGreenBlock (D : Finset Site) (R : Field →L[ℂ] Field) (n : Site) :
    EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card) →L[ℝ]
      EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card) :=
  Maxwell.Defect.realPartOperator (Green.PhysicalCompression.weightedBlock
    (ScalarDefect.edgeEmbedding D) (ScalarDefect.coordinateWeight D) R n)

abbrev LocalModeComplement {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :=
  (Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin k))))ᗮ

/-- The fixed physical input to the uniform reduction. These fields concern
one literal periodic operator and one literal finite defect; no assembled
instance, decoder correctness, or input-dependent inverse is assumed. -/
structure PhysicalPlatform where
  background : PeriodicScalarBackground
  defect : Finset Site
  defect_nonempty : defect.Nonempty
  bulk : Field ≃L[ℂ] Field
  bulk_operator : (bulk : Field →L[ℂ] Field) = background.operator
  bulkGap : ℚ
  rowBound : ℚ
  bulkGap_pos : 0 < bulkGap
  rowBound_pos : 0 < rowBound
  bulk_inverse_bound : ‖(bulk.symm : Field →L[ℂ] Field)‖ ≤ 1 / (bulkGap : ℝ)
  bulk_norm_bound : ‖(bulk : Field →L[ℂ] Field)‖ ≤ (rowBound : ℝ)
  mode : EuclideanSpace ℝ (Fin (ScalarDefect.edges defect).card)
  eigenvalue : ℝ
  mode_unit : ‖mode‖ = 1
  mode_equation : physicalGreenBlock defect (bulk.symm : Field →L[ℂ] Field) 0 mode = eigenvalue • mode
  local_symmetric : (physicalGreenBlock defect (bulk.symm : Field →L[ℂ] Field) 0).toLinearMap.IsSymmetric
  incrementBound : ℚ
  incrementBound_pos : 0 < incrementBound
  increment_reserve : 128 * incrementBound ≤ background.reserve
  eigenvalue_headroom : 2 / (incrementBound : ℝ) < eigenvalue
  defectGap : ℚ
  defectGap_pos : 0 < defectGap
  complement : LocalModeComplement mode ≃L[ℝ] LocalModeComplement mode
  complement_operator : ∀ x : LocalModeComplement mode,
    (complement x : EuclideanSpace ℝ (Fin (ScalarDefect.edges defect).card)) =
      eigenvalue • (x : EuclideanSpace ℝ (Fin (ScalarDefect.edges defect).card)) -
        physicalGreenBlock defect (bulk.symm : Field →L[ℂ] Field) 0 x
  complement_inverse_bound : ‖(complement.symm : LocalModeComplement mode →L[ℝ] LocalModeComplement mode)‖ ≤
    1 / (defectGap : ℝ)
  basis : Matrix Direction Direction ℤ
  basis_injective : Function.Injective basis.mulVec
  spacing : Realization.SpacingPlatform
  radius_floor : SourceDefectLayout.radius defect + 1 ≤ spacing.minimumDistance
  greenConstant : ℚ
  greenConstant_nonneg : 0 ≤ greenConstant
  error_constant : (256 * (greenConstant : ℝ) + 5 + (2 / (defectGap : ℝ)) *
      (64 * (greenConstant : ℝ) + 1)^2) ≤ (spacing.errorConstant : ℝ)
  green_upper : ∀ d : ℕ, spacing.minimumDistance ≤ d → ∀ n : Site, n ≠ 0 →
    ‖Green.PhysicalCompression.weightedBlock (ScalarDefect.edgeEmbedding defect)
      (ScalarDefect.coordinateWeight defect) (bulk.symm : Field →L[ℂ] Field)
      ((d : ℤ) • basis.mulVec n)‖ ≤
      (greenConstant : ℝ) * ((spacing.r : ℝ)^d)^(Realization.latticeLength n)
  green_axial : ∀ d : ℕ, spacing.minimumDistance ≤ d → ∀ j : Direction,
    (spacing.c : ℝ) * (spacing.a : ℝ)^d ≤
      |inner ℝ mode (physicalGreenBlock defect (bulk.symm : Field →L[ℂ] Field)
        ((d : ℤ) • basis.mulVec (unitSite j)) mode)|

namespace PhysicalPlatform

def weightedMode (P : PhysicalPlatform) : EuclideanSpace ℝ (Fin (ScalarDefect.edges P.defect).card) :=
  sqrtWeightOperator (ScalarDefect.coordinateWeight P.defect) P.mode

/-- The scalar parameter record is derived from physical certificates;
the quarter-weights and inverse square-root bound are exact constants. -/
def constants (P : PhysicalPlatform) : Realization.PhysicalConstants where
  gap := P.bulkGap
  rowBound := P.rowBound
  materialHeadroom := P.background.reserve / 128
  weightMinimum := 1 / 4
  inverseWeightBound := 2
  incrementBound := P.incrementBound
  defectGap := P.defectGap
  gap_pos := P.bulkGap_pos
  rowBound_pos := P.rowBound_pos
  materialHeadroom_pos := div_pos P.background.reserve_pos (by norm_num)
  weightMinimum_pos := by norm_num
  inverseWeightBound_pos := by norm_num
  incrementBound_pos := P.incrementBound_pos
  defectGap_pos := P.defectGap_pos

theorem spacing_separates (P : PhysicalPlatform) (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) :
    2 * (SourceDefectLayout.radius P.defect + 1) < 20 * d := by
  have h := P.radius_floor.trans hd
  omega

end PhysicalPlatform
end Maxwell.Composition
