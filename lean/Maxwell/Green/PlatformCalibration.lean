import Maxwell.Green.CalibrationPrecision
import Maxwell.Composition.PeriodicBackground
import Maxwell.Defect.RationalInverseBudget
import Maxwell.Defect.ConcreteFiniteStencil

/-! The finite rational approximation is tied to the actual final periodic
scalar material and inverse of the selected physical platform. -/
namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open scoped InnerProductSpace
set_option maxHeartbeats 600000

/-- Actual rational four-cell coefficients of the final operating material. -/
def rationalMaterial (P : PhysicalPlatform) : Edge → ℚ :=
  rationalEdgeAverage P.background.material

theorem rationalMaterial_binding (P : PhysicalPlatform) (e : Edge) :
    (P.rationalMaterial e : ℝ) = periodicCoefficient P.background.edgeMaterial e := by
  simp only [rationalMaterial, rationalEdgeAverage, periodicCoefficient, edgeMod20,
    PeriodicScalarBackground.edgeMaterial, PeriodicYee.edgeAverage, Rat.cast_div,
    Rat.cast_add, Rat.cast_ofNat]

theorem rationalMaterial_bound (P : PhysicalPlatform) (e : Edge) :
    |(P.rationalMaterial e : ℝ)| ≤ 25 := by
  rw [P.rationalMaterial_binding]
  exact P.background.edge_bound e

theorem rationalOperator_binding (P : PhysicalPlatform) :
    operator P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound 0 =
      P.background.operator := by
  have he : (fun e => (P.rationalMaterial e : ℝ)) = periodicCoefficient P.background.edgeMaterial :=
    funext P.rationalMaterial_binding
  ext v e
  simp [operator, he, PeriodicScalarBackground.operator]

def calibrationGap (P : PhysicalPlatform) : ℚ := min P.bulkGap P.rowBound

theorem calibrationGap_pos (P : PhysicalPlatform) : 0 < P.calibrationGap :=
  lt_min P.bulkGap_pos P.rowBound_pos

theorem calibrationGap_le (P : PhysicalPlatform) : P.calibrationGap ≤ P.rowBound := min_le_right _ _

theorem calibration_spectral_gap (P : PhysicalPlatform) :
    ∀ x ∈ spectrum ℝ (operator P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound 0),
      (P.calibrationGap : ℝ) ≤ |x| := by
  let : Nontrivial Field := by
    refine ⟨⟨lp.single 2 ((0 : Direction), (0 : Site)) (1 : ℂ), 0, ?_⟩⟩
    intro h
    have he := congrArg (fun f : Field => f ((0 : Direction), (0 : Site))) h
    simp at he
  have hu : IsUnit P.background.operator := by
    rw [← P.bulk_operator]
    exact P.bulk.toUnit.isUnit
  have hinv : ‖Ring.inverse P.background.operator‖ ≤ 1 / (P.bulkGap : ℝ) := by
    rw [← PeriodicScalarBackground.bulk_inverse_eq P]
    exact P.bulk_inverse_bound
  have hg := spectral_gap_of_inverse_norm P.background.operator hu 1 P.bulkGap (by norm_num)
    (by exact_mod_cast P.bulkGap_pos) hinv
  intro x hx
  rw [P.rationalOperator_binding] at hx
  have hm : (P.calibrationGap : ℝ) ≤ P.bulkGap := by
    exact_mod_cast (min_le_left P.bulkGap P.rowBound)
  exact hm.trans (by simpa only [div_one] using hg x hx)

theorem calibration_norm_bound (P : PhysicalPlatform) :
    ‖operator P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound 0‖ ≤ (P.rowBound : ℝ) := by
  rw [P.rationalOperator_binding, ← P.bulk_operator]
  exact P.bulk_norm_bound

/-- The one-time exact search depends only on the fixed platform. -/
def calibrationDegree (P : PhysicalPlatform) (b : ℕ) : ℕ :=
  precisionDegree P.calibrationGap P.rowBound P.calibrationGap_pos P.rowBound_pos P.calibrationGap_le b

/-- Computable rational matrix, using only the actual finite material
lookup and compact finite stencil operations. -/
def inverseMatrix {ι : Type*} (P : PhysicalPlatform) (edges : ι → Edge) (b : ℕ) : Matrix ι ι ℚ :=
  compactCompression (coordinateBasis edges) P.rationalMaterial 0
    ((P.rowBound ^ 2)⁻¹) (P.calibrationDegree b)

theorem inverseMatrix_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PhysicalPlatform) (edges : ι ↪ Edge) (b : ℕ) :
    ‖compressionOperator edges (P.bulk.symm : Field →L[ℂ] Field) -
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((P.inverseMatrix edges b).map ((↑) : ℚ → ℂ))‖ ≤
        (1 / 2 : ℝ)^b := by
  rw [PeriodicScalarBackground.bulk_inverse_eq P, ← P.rationalOperator_binding]
  exact compactCompression_binary_error edges P.rationalMaterial 25 (by norm_num)
    P.rationalMaterial_bound 0 P.calibrationGap P.rowBound P.calibrationGap_pos
    P.rowBound_pos P.calibrationGap_le P.calibration_norm_bound P.calibration_spectral_gap b

end Maxwell.Composition.PhysicalPlatform
