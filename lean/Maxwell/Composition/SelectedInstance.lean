import Maxwell.Composition.SelectedPlatform
import Maxwell.Composition.PhysicalCalibrated
import Maxwell.Composition.PhysicalAccuracy
import Maxwell.Composition.PhysicalInstance
import Maxwell.Composition.PhysicalWoodbury
import Maxwell.Composition.PhysicalSoundness
import Maxwell.Composition.SelectedFormat

/-! Rational choices for the literal target, made from the original source
and the fixed selected platform before the random detuning is drawn. -/
noncomputable section
namespace Maxwell.Composition.SelectedInstance
open Maxwell.Realization Maxwell.Defect
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4096

structure Input where
  source : Source.SparseSystem
  precision : ℕ
  sourceBound : ℚ
  accuracy : ℚ
  sourceBound_ge_one : 1 ≤ sourceBound
  accuracy_pos : 0 < accuracy
  nnz_pos : 0 < source.nnz

namespace Input
variable (I : Input) (R : SelectedPlatform)

def epsilon : ℚ := PhysicalAccuracy.epsilon I.source I.precision I.accuracy

theorem epsilon_pos : 0 < I.epsilon :=
  PhysicalAccuracy.epsilon_pos I.source I.precision I.accuracy I.accuracy_pos

theorem epsilon_half : I.epsilon ≤ 1/2 :=
  PhysicalAccuracy.epsilon_le_half I.source I.precision I.accuracy

def logicalBudget : ℚ :=
  PhysicalParameters.logicalInverseBudget I.source I.precision I.sourceBound

theorem logicalBudget_ge_one : 1 ≤ I.logicalBudget :=
  PhysicalParameters.logicalInverseBudget_ge_one I.source I.precision I.sourceBound I.sourceBound_ge_one

def distance : ℕ := PhysicalParameters.distance R.physical I.source I.precision
  I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos

theorem distance_floor : R.physical.coreFloor ≤ I.distance R :=
  PhysicalParameters.distance_coreFloor R.physical I.source I.precision
    I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos

theorem distance_minimum : R.physical.spacing.minimumDistance ≤ I.distance R :=
  R.physical.coreFloor_minimum.trans (I.distance_floor R)

def zeta : ℚ := R.physical.spacing.zeta (I.distance R)
def alpha : ℚ := R.physical.spacing.alpha (I.distance R)

theorem zeta_pos : 0 < I.zeta R := R.physical.spacing.zeta_pos _
theorem alpha_pos : 0 < I.alpha R := R.physical.spacing.alpha_pos _
theorem zeta_one : I.zeta R ≤ 1 :=
  PhysicalParameters.zeta_le_one R.physical I.source I.precision
    I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos

theorem zeta_sq_alpha : (I.zeta R)^2 ≤ I.alpha R :=
  PhysicalParameters.zeta_sq_le_alpha R.physical I.source I.precision
    I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos
    (I.epsilon_half.trans (by norm_num))

def backgroundBudget : ℚ :=
  PhysicalParameters.backgroundInverseBudget R.physical I.source I.precision
    I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos

theorem backgroundBudget_ge_one : 1 ≤ I.backgroundBudget R :=
  PhysicalParameters.backgroundInverseBudget_ge_one R.physical I.source I.precision
    I.sourceBound I.epsilon I.sourceBound_ge_one I.epsilon_pos I.nnz_pos

theorem backgroundBudget_pos : 0 < I.backgroundBudget R :=
  lt_of_lt_of_le zero_lt_one (I.backgroundBudget_ge_one R)

def fullBudget : ℚ := R.physical.constants.fullInverseBudget
  I.logicalBudget (I.alpha R) (I.backgroundBudget R)

theorem fullBudget_pos : 0 < I.fullBudget R :=
  R.physical.constants.fullInverseBudget_pos _ _ _
    (lt_of_lt_of_le zero_lt_one I.logicalBudget_ge_one) (I.alpha_pos R) (I.backgroundBudget_pos R)

def sourceTolerance : ℚ := R.physical.constants.calibrationUnit I.epsilon
  (I.alpha R) (I.backgroundBudget R) (I.fullBudget R) I.epsilon_pos
  (I.alpha_pos R) (I.backgroundBudget_pos R) (I.fullBudget_pos R)

theorem sourceTolerance_pos : 0 < I.sourceTolerance R := precisionUnit_pos _ _
theorem sourceTolerance_one : I.sourceTolerance R ≤ 1 := precisionUnit_le_one _ _

def coordinates : PhysicalSource.Local R.physical → ℚ :=
  PhysicalCalibrated.coordinates R.physical R.modeApproximation (I.sourceTolerance R) (I.distance R)

theorem coordinates_error :
    ‖PhysicalSource.realVector (I.coordinates R)-R.physical.weightedMode‖ ≤ I.sourceTolerance R :=
  PhysicalCalibrated.coordinates_error R.physical R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    (I.sourceTolerance R) (I.sourceTolerance_pos R) (I.distance R)

theorem coordinates_norm : ‖PhysicalSource.realVector (I.coordinates R)‖ ≤ 2 := by
  have he := I.coordinates_error R
  have ht : (I.sourceTolerance R : ℝ) ≤ 1 := by exact_mod_cast I.sourceTolerance_one R
  have hn := norm_le_norm_add_norm_sub R.physical.weightedMode (PhysicalSource.realVector (I.coordinates R))
  rw [norm_sub_rev] at hn
  linarith [R.physical.weightedMode_norm_le]

theorem coordinates_source_budget :
    ‖PhysicalSource.realVector (I.coordinates R)-R.physical.weightedMode‖ ≤
      (1/4:ℝ)*I.epsilon/(32768*R.physical.rowBound*I.backgroundBudget R) := by
  apply (I.coordinates_error R).trans
  have hb : I.sourceTolerance R ≤
      (1/4:ℚ)*I.epsilon/(32768*R.physical.rowBound*I.backgroundBudget R) :=
    (R.physical.constants.calibrationUnit_bounds I.epsilon
      (I.alpha R) (I.backgroundBudget R) (I.fullBudget R) I.epsilon_pos
      (I.alpha_pos R) (I.backgroundBudget_pos R) (I.fullBudget_pos R)).1
  have hc := (Rat.cast_le (K := ℝ)).mpr hb
  push_cast at hc ⊢
  exact hc

theorem coordinates_read_budget :
    ‖PhysicalSource.realVector (I.coordinates R)-R.physical.weightedMode‖ ≤
      (I.epsilon:ℝ)/(1024*R.physical.incrementBound*I.alpha R*R.physical.rowBound*2*I.fullBudget R) := by
  apply (I.coordinates_error R).trans
  exact_mod_cast (R.physical.constants.calibrationUnit_bounds I.epsilon
    (I.alpha R) (I.backgroundBudget R) (I.fullBudget R) I.epsilon_pos
    (I.alpha_pos R) (I.backgroundBudget_pos R) (I.fullBudget_pos R)).2

def coupling : Maxwell.Spectral.Lattice.Direction → ℚ :=
  PhysicalCalibrated.coupling R.physical R.modeApproximation (I.sourceTolerance R) (I.distance R)

theorem coupling_lower (j : Maxwell.Spectral.Lattice.Direction) :
    3*(I.alpha R : ℝ) ≤ |(I.coupling R j : ℝ)| :=
  PhysicalCalibrated.coupling_lower R.physical R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    (I.sourceTolerance R) (I.sourceTolerance_pos R) (I.distance R) (I.distance_floor R)
    (I.zeta_sq_alpha R) j

theorem coupling_upper (j : Maxwell.Spectral.Lattice.Direction) :
    |(I.coupling R j : ℝ)| ≤ (((R.physical.greenConstant+1)*I.zeta R : ℚ):ℝ) :=
  PhysicalCalibrated.coupling_upper R.physical R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    (I.sourceTolerance R) (I.sourceTolerance_pos R) (I.distance R) (I.distance_floor R) j

theorem coupling_error (j : Maxwell.Spectral.Lattice.Direction) :
    |(I.coupling R j : ℝ)+PhysicalBright.axial R.physical (I.distance R) j| ≤ (I.zeta R : ℝ)^2 :=
  PhysicalCalibrated.coupling_error R.physical R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    (I.sourceTolerance R) (I.sourceTolerance_pos R) (I.distance R) (I.distance_floor R) j

def increment : SourceDecoration.Vertex I.source I.precision → ℚ :=
  PhysicalCalibrated.increment R.physical R.modeApproximation
    (I.sourceTolerance R) (I.distance R) I.source I.precision

theorem increment_spec (i : SourceDecoration.Vertex I.source I.precision) :
    0 < I.increment R i ∧ I.increment R i ≤ R.physical.incrementBound ∧
    |(I.increment R i : ℝ)⁻¹-(R.physical.eigenvalue+
      (PhysicalDiagonal.diagonal I.source I.precision (I.alpha R) (I.coupling R) i : ℝ))| ≤
      (I.zeta R : ℝ)^2 ∧
    Maxwell.rationalBitLength (I.increment R i) ≤
      4*(I.zeta R).den.size+R.physical.reciprocalBitOverhead :=
  PhysicalCalibrated.increment_spec R.physical R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    (I.sourceTolerance R) (I.sourceTolerance_pos R) (I.distance R) (I.distance_floor R) I.source I.precision i

theorem increment_bounds (i : SourceDecoration.Vertex I.source I.precision) :
    0 ≤ I.increment R i ∧ I.increment R i ≤ R.physical.incrementBound :=
  ⟨(I.increment_spec R i).1.le, (I.increment_spec R i).2.1⟩

theorem increment_ne_zero (i : SourceDecoration.Vertex I.source I.precision) :
    I.increment R i ≠ 0 := ne_of_gt (I.increment_spec R i).1

def residualTolerance : ℚ := R.physical.constants.residualUnit
  I.epsilon (I.backgroundBudget R) I.epsilon_pos (I.backgroundBudget_pos R)

theorem residualTolerance_pos : 0 < I.residualTolerance R := precisionUnit_pos _ _

theorem residualTolerance_budget :
    I.residualTolerance R ≤ I.epsilon/(8192*R.physical.rowBound*2*I.backgroundBudget R) :=
  (R.physical.constants.residualUnit_bounds I.epsilon (I.backgroundBudget R)
    I.epsilon_pos (I.backgroundBudget_pos R)).2

theorem residualTolerance_half : I.residualTolerance R ≤ 1/2 := by
  apply (I.residualTolerance_budget R).trans
  apply le_trans _ I.epsilon_half
  apply div_le_self I.epsilon_pos.le
  rw [R.rowBound_eq]
  have := I.backgroundBudget_ge_one R
  linarith

theorem spacing_budget :
    (R.physical.spacing.errorConstant : ℝ)*(I.zeta R : ℝ)^2 ≤
      (I.alpha R : ℝ)*I.epsilon/(4096*SourceMediator.inverseBudget I.source I.precision I.sourceBound) :=
  PhysicalParameters.error_budget_real R.physical I.source I.precision I.sourceBound
    I.epsilon I.sourceBound_ge_one I.epsilon_pos

theorem logical_budget :
    (SourceRecovery.residualFactor I.source I.precision : ℚ)*I.epsilon ≤ I.accuracy :=
  PhysicalAccuracy.epsilon_residualFactor I.source I.precision I.accuracy I.accuracy_pos

theorem read_budget (hunit : IsUnit (Source.realMatrix I.source)) (hb : I.source.source ≠ 0) :
    (I.epsilon:ℝ)*‖PhysicalSource.exactLogicalSource I.source I.precision‖*I.source.nnz ≤ I.accuracy := by
  rw [PhysicalSource.exactLogicalSource_norm]
  have hg := PhysicalAccuracy.source_norm_le_nnz I.source I.precision hunit hb I.nnz_pos
  have he : (I.epsilon:ℝ)*(I.source.nnz:ℝ)^2 ≤ I.accuracy := by
    exact_mod_cast PhysicalAccuracy.epsilon_nnz_sq I.source I.precision I.accuracy I.accuracy_pos
  have hp : (0:ℝ) ≤ I.epsilon := by exact_mod_cast I.epsilon_pos.le
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hp)
    (Nat.cast_nonneg (α := ℝ) I.source.nnz)
  nlinarith

abbrev box := PhysicalGram.box R.physical I.source I.precision (I.distance R)
  (I.zeta R) (I.zeta_pos R) (I.zeta_one R)

theorem fullBudget_cast : (I.fullBudget R : ℝ) =
    PhysicalSoundness.fullBudget R.physical I.source I.precision (I.distance R)
      (I.zeta R) (I.zeta_pos R) (I.zeta_one R) I.sourceBound := by
  have hK : (I.logicalBudget : ℝ) =
      SourceMediator.inverseBudget I.source I.precision I.sourceBound :=
    PhysicalParameters.logicalInverseBudget_cast I.source I.precision I.sourceBound
  simp only [fullBudget, PhysicalConstants.fullInverseBudget,
    PhysicalConstants.modeInverseBudget, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat, hK]
  rfl

def amplitude : ℚ := 6*I.alpha R*R.physical.rowBound*I.fullBudget R*I.source.nnz

def format : Target.FixedPointFormat := selectedFormat R.physical I.epsilon I.epsilon_pos
  I.source.n (ScalarDefect.edges R.physical.defect).card (I.amplitude R)

theorem format_access :
    2*(R.physical.incrementBound:ℝ)*((I.source.n:ℝ)*(ScalarDefect.edges R.physical.defect).card)/
      (2:ℝ)^(I.format R).fractionalBits ≤ (I.epsilon:ℝ)/4096 := by
  have h := selectedFormat_error_bound R.physical I.epsilon I.epsilon_pos I.source.n
    (ScalarDefect.edges R.physical.defect).card (I.amplitude R)
  exact_mod_cast h

theorem format_range (hunit : IsUnit (Source.realMatrix I.source)) (hb : I.source.source ≠ 0) :
    6*(I.alpha R:ℝ)*R.physical.rowBound*I.fullBudget R*
      ‖PhysicalSource.exactLogicalSource I.source I.precision‖ < (2:ℝ)^(I.format R).integerBits := by
  have h := selectedFormat_amplitude R.physical I.epsilon I.epsilon_pos I.source.n
    (ScalarDefect.edges R.physical.defect).card (I.amplitude R)
  have hR : (I.amplitude R : ℝ) < (2:ℝ)^(I.format R).integerBits := by exact_mod_cast h
  apply lt_of_le_of_lt _ hR
  have hg := PhysicalAccuracy.source_norm_le_nnz I.source I.precision hunit hb I.nnz_pos
  rw [PhysicalSource.exactLogicalSource_norm]
  have ha : (0:ℝ) < I.alpha R := by exact_mod_cast I.alpha_pos R
  have hrow : (0:ℝ) < R.physical.rowBound := by exact_mod_cast R.physical.rowBound_pos
  have hQA : (0:ℝ) < I.fullBudget R := by exact_mod_cast I.fullBudget_pos R
  simpa only [amplitude, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using
    mul_le_mul_of_nonneg_left hg (show 0 ≤ 6*(I.alpha R:ℝ)*R.physical.rowBound*I.fullBudget R by positivity)

abbrev target (J : ℕ) (j : Fin J) : Target.Instance I.source.n :=
  PhysicalInstance.target R.physical I.source I.precision (I.distance R)
    (I.zeta R) (I.zeta_pos R) (I.zeta_one R) (I.distance_minimum R) J j
    (I.alpha R) I.epsilon (I.backgroundBudget R) (I.alpha_pos R) I.epsilon_pos
    (I.backgroundBudget_pos R) (I.coordinates R) (I.increment R) (I.increment_bounds R)
    (I.residualTolerance R) (I.residualTolerance_pos R) (I.format R)

end Input
end Maxwell.Composition.SelectedInstance
