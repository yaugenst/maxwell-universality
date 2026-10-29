import Maxwell.Green.IntegerCoupling
import Maxwell.Green.SourceRounding

/-! One computed source vector supplies the physical source/readout and all
three axial calibrations. The source and coupling precision requests are
combined before the fixed-mode refinement is run. -/
namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
set_option maxHeartbeats 600000

def calibrationDigits (P : PhysicalPlatform) (sourceTolerance ζ : ℚ) (d : ℕ) : ℕ :=
  max (Green.denominatorPrecision sourceTolerance) (P.couplingPrecision (P.axialBudget ζ d))

def sourceCoordinates (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (sourceTolerance ζ : ℚ) (d : ℕ) : Fin (ScalarDefect.edges P.defect).card → ℚ :=
  SourceRounding.roundedWeightedVector (ScalarDefect.coordinateWeight P.defect) q
    (P.calibrationDigits sourceTolerance ζ d)

theorem calibrationDigits_source (P : PhysicalPlatform) (sourceTolerance ζ : ℚ)
    (hsource : 0 < sourceTolerance) (d : ℕ) :
    (1/2 : ℝ)^P.calibrationDigits sourceTolerance ζ d ≤ sourceTolerance := by
  have hp : (1/2 : ℝ)^P.calibrationDigits sourceTolerance ζ d ≤
      (1/2 : ℝ)^Green.denominatorPrecision sourceTolerance :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mpr (le_max_left _ _)
  have hs := (Rat.cast_le (K := ℝ)).mpr (Green.denominatorPrecision_error sourceTolerance hsource)
  exact hp.trans (by simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hs)

theorem calibrationDigits_coupling (P : PhysicalPlatform) (sourceTolerance ζ : ℚ) (d : ℕ) :
    (1/2 : ℝ)^P.calibrationDigits sourceTolerance ζ d ≤
      (1/2 : ℝ)^P.couplingPrecision (P.axialBudget ζ d) :=
  (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mpr (le_max_right _ _)

theorem sourceCoordinates_error (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (sourceTolerance ζ : ℚ) (hsource : 0 < sourceTolerance) (d : ℕ) :
    ‖rationalCoordinates (P.sourceCoordinates q sourceTolerance ζ d)-P.weightedMode‖ ≤
      sourceTolerance ∧
    ‖rationalCoordinates (P.sourceCoordinates q sourceTolerance ζ d)-P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision (P.axialBudget ζ d) := by
  have hq : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ ((2 : ℝ)^b)⁻¹ := by
    intro b
    simpa only [one_div, inv_pow] using hqerror b
  have h := SourceRounding.roundedWeightedVector_error (ScalarDefect.coordinateWeight P.defect)
    q P.mode (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds P.defect i).1)
    (fun i => (ScalarDefect.coordinateWeight_bounds P.defect i).2) P.mode_unit hqnorm hq
    (P.calibrationDigits sourceTolerance ζ d)
  exact ⟨h.trans (P.calibrationDigits_source sourceTolerance ζ hsource d),
    h.trans (P.calibrationDigits_coupling sourceTolerance ζ d)⟩

theorem sourceCoordinates_bits (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (sourceTolerance ζ : ℚ) (d : ℕ) (i : Fin (ScalarDefect.edges P.defect).card) :
    Maxwell.rationalBitLength (P.sourceCoordinates q sourceTolerance ζ d i) ≤
      4 * P.calibrationDigits sourceTolerance ζ d +
        2*((ScalarDefect.edges P.defect).card+1).size+5 := by
  apply SourceRounding.roundedWeightedVector_bits (ScalarDefect.coordinateWeight P.defect)
    q P.mode (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds P.defect i).1)
    (fun i => (ScalarDefect.coordinateWeight_bounds P.defect i).2) P.mode_unit hqnorm
  intro b
  simpa only [one_div, inv_pow] using hqerror b

def calibratedAxis (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (sourceTolerance ζ : ℚ) (d : ℕ) (j : Direction) : ℚ :=
  P.integerSignedCoupling (P.sourceCoordinates q sourceTolerance ζ d)
    ((d : ℤ) • P.basis.mulVec (unitSite j)) (P.couplingPrecision (P.axialBudget ζ d))

theorem calibratedAxis_error (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (sourceTolerance ζ : ℚ) (hsource : 0 < sourceTolerance) (hζ : 0 < ζ)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction) :
    |(P.calibratedAxis q sourceTolerance ζ d j : ℝ) -
      (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
        ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode))| ≤ (ζ : ℝ)^2 ∧
    (P.spacing.c : ℝ)*(P.spacing.a : ℝ)^d/2 ≤
      |(P.calibratedAxis q sourceTolerance ζ d j : ℝ)| := by
  unfold calibratedAxis
  rw [P.integerSignedCoupling_eq]
  exact P.signedCoupling_axial ζ hζ d hd j _
    (P.sourceCoordinates_error q hqnorm hqerror sourceTolerance ζ hsource d).2

theorem calibrationDigits_bound (P : PhysicalPlatform) (sourceTolerance ζ : ℚ) (d : ℕ) :
    P.calibrationDigits sourceTolerance ζ d ≤ sourceTolerance.den.size +
      2*ζ.den.size+d*P.spacing.a.den.size+P.couplingBitOverhead := by
  have h := P.couplingPrecision_axial_bound ζ d
  unfold calibrationDigits Green.denominatorPrecision
  omega

end Maxwell.Composition.PhysicalPlatform
