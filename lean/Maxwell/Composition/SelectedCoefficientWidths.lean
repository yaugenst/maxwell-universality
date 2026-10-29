import Maxwell.Composition.SelectedWidths

/-! Actual stored mode and defect-increment coefficients have logarithmic
width before any draw is made. -/
noncomputable section
namespace Maxwell.Composition.SelectedCoefficientWidths
open Maxwell.Realization Maxwell.Composition.SelectedWidths
open Maxwell.Composition.SelectedSpacingBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

theorem precisionUnit_den (budget : ℚ) (hbudget : 0 < budget) :
    (precisionUnit budget hbudget).den.size = precisionBits budget hbudget+1 := by
  unfold precisionUnit
  rw [one_div, Rat.den_inv_of_ne_zero (by positivity)]
  rw [show (2:ℚ)^precisionBits budget hbudget = ((2^precisionBits budget hbudget:ℕ):ℚ) by norm_cast]
  simp only [Rat.num_natCast, Int.natAbs_natCast]
  simpa only [Maxwell.Codec.unsignedBitLength_eq_size] using
    Maxwell.Dyadic.denominator_bitLength (precisionBits budget hbudget)

def distanceCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  distanceBase R+distanceSlope p R
def zetaCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  1+R.physical.spacing.r.den.size*distanceCoefficient p R
def digitsCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  calibrationExponent p R+1+2*zetaCoefficient p R+
    distanceCoefficient p R*R.physical.spacing.a.den.size+R.physical.couplingBitOverhead
def coordinateCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  4*digitsCoefficient p R+2*(localCount R+1).size+5
def incrementCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  4*zetaCoefficient p R+R.physical.reciprocalBitOverhead

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm
local notation "B" => unsignedBitLength (2+S.nnz)

theorem distance_bits (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).distance R ≤ distanceCoefficient p R*B := by
  have h := distance_bound p S hm R hm2 hunit
  have hb := clog_le_inputBitLength S.nnz
  have hp := inputBitLength_pos S.nnz
  unfold distanceCoefficient
  nlinarith [Nat.mul_le_mul_left (distanceSlope p R) hb,
    Nat.mul_le_mul_left (distanceBase R) hp]

theorem zeta_den (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).zeta R).den.size ≤ zetaCoefficient p R*B := by
  have h := Green.pow_den_size R.physical.spacing.r ((I).distance R)
  have hd := distance_bits p S hm R hm2 hunit
  have hp := inputBitLength_pos S.nnz
  change ((I).zeta R).den.size ≤ _ at h
  unfold zetaCoefficient
  nlinarith [Nat.mul_le_mul_left R.physical.spacing.r.den.size hd]

theorem sourceTolerance_den (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).sourceTolerance R).den.size ≤ (calibrationExponent p R+1)*B := by
  have h := calibration_precision p S hm R hm2 hunit
  have hb := clog_le_inputBitLength S.nnz
  have hp := inputBitLength_pos S.nnz
  unfold SelectedInstance.Input.sourceTolerance PhysicalConstants.calibrationUnit
  rw [precisionUnit_den]
  nlinarith [Nat.mul_le_mul_left (calibrationExponent p R) hb]

theorem calibration_digits (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    R.physical.calibrationDigits ((I).sourceTolerance R) ((I).zeta R) ((I).distance R) ≤
      digitsCoefficient p R*B := by
  have h := R.physical.calibrationDigits_bound ((I).sourceTolerance R) ((I).zeta R) ((I).distance R)
  have hs := sourceTolerance_den p S hm R hm2 hunit
  have hz := zeta_den p S hm R hm2 hunit
  have hd := distance_bits p S hm R hm2 hunit
  have hp := inputBitLength_pos S.nnz
  unfold digitsCoefficient
  nlinarith [Nat.mul_le_mul_right R.physical.spacing.a.den.size hd,
    Nat.mul_le_mul_left R.physical.couplingBitOverhead hp]

theorem coordinate_bits (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (i : PhysicalSource.Local R.physical) :
    rationalBitLength ((I).coordinates R i) ≤ coordinateCoefficient p R*B := by
  have h := R.physical.sourceCoordinates_bits R.modeApproximation
    (fun b => (R.modeApproximation_spec b).1) (fun b => (R.modeApproximation_spec b).2)
    ((I).sourceTolerance R) ((I).zeta R) ((I).distance R) i
  have hc := calibration_digits p S hm R hm2 hunit
  have hp := inputBitLength_pos S.nnz
  change rationalBitLength ((I).coordinates R i) ≤ _ at h
  unfold coordinateCoefficient localCount
  nlinarith [Nat.mul_le_mul_left (2*((Defect.ScalarDefect.edges R.physical.defect).card+1).size+5) hp]

theorem increment_bits (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (i : SourceDecoration.Vertex S (I).precision) :
    rationalBitLength ((I).increment R i) ≤ incrementCoefficient p R*B := by
  have h := ((I).increment_spec R i).2.2.2
  have hz := zeta_den p S hm R hm2 hunit
  have hp := inputBitLength_pos S.nnz
  unfold incrementCoefficient
  nlinarith [Nat.mul_le_mul_left R.physical.reciprocalBitOverhead hp]

theorem short_of_bits {q : ℚ} {b : ℕ} (h : rationalBitLength q ≤ b) :
    Source.ShortRational (b:ℝ) q := by
  constructor <;> exact_mod_cast (show _ ≤ b from (by unfold rationalBitLength at h; omega))

theorem coordinates_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (i : PhysicalSource.Local R.physical) :
    Source.ShortRational ((coordinateCoefficient p R*B:ℕ):ℝ) ((I).coordinates R i) :=
  short_of_bits (coordinate_bits p S hm R hm2 hunit i)

theorem increments_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (i : SourceDecoration.Vertex S (I).precision) :
    Source.ShortRational ((incrementCoefficient p R*B:ℕ):ℝ) ((I).increment R i) :=
  short_of_bits (increment_bits p S hm R hm2 hunit i)

end Maxwell.Composition.SelectedCoefficientWidths
