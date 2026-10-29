import Maxwell.Green.EigenvalueCalibration
import Maxwell.Green.CalibrationOutputs
import Maxwell.Composition.PhysicalDiagonal
import Maxwell.Composition.PhysicalBright.Nearest

/-! The literal source, axial couplings and scalar strengths computed from
one refinement of the selected physical mode. -/
noncomputable section
namespace Maxwell.Composition.PhysicalCalibrated
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
set_option maxHeartbeats 600000

variable (P : PhysicalPlatform)
variable (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
variable (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
variable (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
variable (sourceTolerance : ℚ) (hsource : 0 < sourceTolerance)
variable (d : ℕ) (hd : P.coreFloor ≤ d)

def coordinates : Fin (ScalarDefect.edges P.defect).card → ℚ :=
  P.sourceCoordinates q sourceTolerance (P.spacing.zeta d) d

def coupling : Direction → ℚ :=
  P.calibratedAxis q sourceTolerance (P.spacing.zeta d) d

include hqnorm hqerror hsource in
theorem coordinates_error :
    ‖PhysicalPlatform.rationalCoordinates (coordinates P q sourceTolerance d)-P.weightedMode‖ ≤
      sourceTolerance :=
  (P.sourceCoordinates_error q hqnorm hqerror sourceTolerance (P.spacing.zeta d) hsource d).1

include hqnorm hqerror hsource hd in
theorem coupling_error (j : Direction) :
    |(coupling P q sourceTolerance d j : ℝ)+PhysicalBright.axial P d j| ≤
      (P.spacing.zeta d : ℝ)^2 := by
  have hh := (P.calibratedAxis_error q hqnorm hqerror sourceTolerance
    (P.spacing.zeta d) hsource (P.spacing.zeta_pos d) d (P.coreFloor_minimum.trans hd) j).1
  simpa only [coupling, PhysicalBright.axial, sub_neg_eq_add] using hh

include hqnorm hqerror hsource hd in
theorem coupling_lower (hsmall : (P.spacing.zeta d)^2 ≤ P.spacing.alpha d) (j : Direction) :
    3*(P.spacing.alpha d : ℝ) ≤ |(coupling P q sourceTolerance d j : ℝ)| := by
  unfold coupling PhysicalPlatform.calibratedAxis
  rw [P.integerSignedCoupling_eq]
  exact P.signedCoupling_axial_three_alpha d (P.coreFloor_minimum.trans hd) j _
    (P.sourceCoordinates_error q hqnorm hqerror sourceTolerance (P.spacing.zeta d) hsource d).2
    hsmall

include hqnorm hqerror hsource hd in
theorem coupling_upper (j : Direction) :
    |(coupling P q sourceTolerance d j : ℝ)| ≤
      (((P.greenConstant+1)*P.spacing.zeta d : ℚ) : ℝ) := by
  have hh := P.signedCoupling_axial_upper d (P.coreFloor_minimum.trans hd) j _
    (P.sourceCoordinates_error q hqnorm hqerror sourceTolerance (P.spacing.zeta d) hsource d).2
  have hz0 : (0 : ℝ) ≤ P.spacing.zeta d := by exact_mod_cast (P.spacing.zeta_pos d).le
  have hz1 : (P.spacing.zeta d : ℝ) ≤ 1 := by
    have hh : P.spacing.zeta d ≤ 1 := (P.coreFloor_small d hd).1.trans (by norm_num)
    exact_mod_cast hh
  have hs : (P.spacing.zeta d : ℝ)^2 ≤ (P.spacing.zeta d : ℝ) := by nlinarith
  unfold coupling PhysicalPlatform.calibratedAxis
  rw [P.integerSignedCoupling_eq]
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_one]
  linarith

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

def increment (i : SourceDecoration.Vertex S precision) : ℚ :=
  (P.calibratedIncrement q (P.spacing.zeta d) (P.spacing.zeta_pos d)
    (PhysicalDiagonal.diagonal S precision (P.spacing.alpha d) (coupling P q sourceTolerance d) i)).value

include hqnorm hqerror hsource hd in
theorem diagonal_bound (i : SourceDecoration.Vertex S precision) :
    |(PhysicalDiagonal.diagonal S precision (P.spacing.alpha d)
      (coupling P q sourceTolerance d) i : ℝ)| ≤ 1/(2*(P.incrementBound : ℝ)) := by
  apply (PhysicalDiagonal.diagonal_bound S precision P d hd
    (coupling P q sourceTolerance d) (coupling_upper P q hqnorm hqerror sourceTolerance hsource d hd) i).trans
  have hh : P.tuningMargin ≤ 1/(2*P.incrementBound) := min_le_right _ _
  exact_mod_cast hh

include hqnorm hqerror hsource hd in
theorem increment_spec (i : SourceDecoration.Vertex S precision) :
    0 < increment P q sourceTolerance d S precision i ∧
      increment P q sourceTolerance d S precision i ≤ P.incrementBound ∧
      |(increment P q sourceTolerance d S precision i : ℝ)⁻¹-
        (P.eigenvalue+(PhysicalDiagonal.diagonal S precision (P.spacing.alpha d)
          (coupling P q sourceTolerance d) i : ℝ))| ≤ (P.spacing.zeta d : ℝ)^2 ∧
      Maxwell.rationalBitLength (increment P q sourceTolerance d S precision i) ≤
        4*(P.spacing.zeta d).den.size+P.reciprocalBitOverhead :=
  P.calibratedIncrement_spec q hqnorm hqerror _ (P.spacing.zeta_pos d) _
    (diagonal_bound P q hqnorm hqerror sourceTolerance hsource d hd S precision i)

include hqnorm hqerror hsource hd in
theorem increment_material (i : SourceDecoration.Vertex S precision) (c : Cell20) :
    1 ≤ P.background.material c + 64*increment P q sourceTolerance d S precision i ∧
      P.background.material c + 64*increment P q sourceTolerance d S precision i ≤
        25-64*P.incrementBound :=
  P.roundedReciprocal_material _ (P.spacing.zeta_pos d) _ _
    (P.calibratedEigenvalue_error q hqnorm hqerror _ (P.spacing.zeta_pos d))
    (diagonal_bound P q hqnorm hqerror sourceTolerance hsource d hd S precision i) c

end Maxwell.Composition.PhysicalCalibrated
