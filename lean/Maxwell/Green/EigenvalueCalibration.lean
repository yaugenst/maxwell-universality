import Maxwell.Green.BinaryCompression
import Maxwell.Green.ReciprocalBitBounds
import Maxwell.Defect.WeightedModeRefinement

/-! Computed rational Rayleigh calibration of the same selected mode, and
its use in the emitted scalar-cell tuning. -/
namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression
set_option maxHeartbeats 600000

theorem weightedInverseCompression_binding (P : PhysicalPlatform) :
    weightedInverseCompression (ScalarDefect.edgeEmbedding P.defect) P.rationalMaterial
      25 (by norm_num) P.rationalMaterial_bound 0 (ScalarDefect.coordinateWeight P.defect) =
      physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0 := by
  rw [weightedInverseCompression_realPart, P.rationalOperator_binding,
    ← PeriodicScalarBackground.bulk_inverse_eq P]
  have hzero : translatedEmbedding (ScalarDefect.edgeEmbedding P.defect) 0 =
      ScalarDefect.edgeEmbedding P.defect := by
    apply Function.Embedding.ext
    intro i
    change ((ScalarDefect.edgeEmbedding P.defect i).1,
      (ScalarDefect.edgeEmbedding P.defect i).2 - 20 • (0 : Site)) =
      ScalarDefect.edgeEmbedding P.defect i
    simp
  unfold physicalGreenBlock weightedBlock
  rw [hzero, sourceCompression_apply]

def modeMatrix (P : PhysicalPlatform) (b : ℕ) :
    Matrix (Fin (ScalarDefect.edges P.defect).card) (Fin (ScalarDefect.edges P.defect).card) ℚ :=
  binaryCompressionMatrix (ScalarDefect.edgeEmbedding P.defect) P.rationalMaterial 0
    P.calibrationGap P.rowBound P.calibrationGap_pos P.rowBound_pos P.calibrationGap_le
    (ScalarDefect.coordinateWeight P.defect) b

theorem modeMatrix_error (P : PhysicalPlatform) (b : ℕ) :
    ‖rationalOperator (P.modeMatrix b) -
      physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0‖ ≤
      (1+2*(P.calibrationGap : ℝ)⁻¹)*(1/2 : ℝ)^b := by
  rw [← P.weightedInverseCompression_binding]
  exact binaryCompressionMatrix_error (ScalarDefect.edgeEmbedding P.defect)
    P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound 0 P.calibrationGap
    P.rowBound P.calibrationGap_pos P.rowBound_pos P.calibrationGap_le
    (ScalarDefect.coordinateWeight P.defect)
    (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds P.defect i).1)
    (fun i => (ScalarDefect.coordinateWeight_bounds P.defect i).2)
    P.calibration_norm_bound P.calibration_spectral_gap b

theorem physical_mode_block_norm (P : PhysicalPlatform) :
    ‖physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0‖ ≤
      (P.calibrationGap : ℝ)⁻¹ := by
  rw [← P.weightedInverseCompression_binding]
  exact weightedInverseCompression_norm_le (ScalarDefect.edgeEmbedding P.defect)
    P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound 0
    (ScalarDefect.coordinateWeight P.defect)
    (fun i => (ScalarDefect.coordinateWeight_bounds P.defect i).2)
    P.calibrationGap (by exact_mod_cast P.calibrationGap_pos) P.calibration_spectral_gap

def eigenvalueErrorConstant (P : PhysicalPlatform) : ℚ := 1+4*P.calibrationGap⁻¹

theorem eigenvalueErrorConstant_pos (P : PhysicalPlatform) : 0 < P.eigenvalueErrorConstant := by
  have := P.calibrationGap_pos
  unfold eigenvalueErrorConstant
  positivity

def eigenvalueDigits (P : PhysicalPlatform) (ζ : ℚ) : ℕ :=
  Green.denominatorPrecision (P.eigenvalueBudget ζ / P.eigenvalueErrorConstant)

def eigenvalueBitOverhead (P : PhysicalPlatform) : ℕ :=
  (1 / (4 * P.incrementBound)).den.size +
    P.eigenvalueErrorConstant.num.natAbs.size + 3

theorem eigenvalueDigits_bound (P : PhysicalPlatform) (ζ : ℚ) :
    P.eigenvalueDigits ζ ≤ 2*ζ.den.size + P.eigenvalueBitOverhead := by
  have hζ := Green.pow_den_size ζ 2
  have hd := Green.div_den_size (ζ^2) 2 (by norm_num)
  have hm := Green.min_den_size (ζ^2/2) (1/(4*P.incrementBound))
  have hfinal := Green.div_den_size (P.eigenvalueBudget ζ) P.eigenvalueErrorConstant
    P.eigenvalueErrorConstant_pos.ne'
  norm_num at hd
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo] at hd
  rw [Rat.den_pow] at hζ
  unfold eigenvalueDigits Green.denominatorPrecision eigenvalueBitOverhead
  unfold eigenvalueBudget at hfinal ⊢
  omega

def calibratedEigenvalue (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ) (ζ : ℚ) : ℚ :=
  WeightedModeRefinement.eigenvalue P.modeMatrix q (P.eigenvalueDigits ζ)

theorem calibratedEigenvalue_error (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (ζ : ℚ) (hζ : 0 < ζ) :
    |(P.calibratedEigenvalue q ζ : ℝ)-P.eigenvalue| ≤ (P.eigenvalueBudget ζ : ℝ) := by
  have hq : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ ((2 : ℝ)^b)⁻¹ := by
    intro b
    simpa only [one_div, inv_pow] using hqerror b
  have hT : ∀ b, ‖rationalOperator (P.modeMatrix b)-
      physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0‖ ≤
      (1+2*(P.calibrationGap : ℝ)⁻¹)*((2 : ℝ)^b)⁻¹ := by
    intro b
    simpa only [one_div, inv_pow] using P.modeMatrix_error b
  have he := WeightedModeRefinement.eigenvalue_spec
    (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0) P.modeMatrix q P.mode
    P.eigenvalue (1+2*(P.calibrationGap : ℝ)⁻¹) P.mode_unit P.mode_equation hqnorm hq hT
    (P.eigenvalueDigits ζ)
  have hconstant : 1+2*(P.calibrationGap : ℝ)⁻¹+
      2*‖physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0‖ ≤
      (P.eigenvalueErrorConstant : ℝ) := by
    simp only [eigenvalueErrorConstant, Rat.cast_add, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_inv]
    linarith [P.physical_mode_block_norm]
  have hp := Green.denominatorPrecision_error (P.eigenvalueBudget ζ/P.eigenvalueErrorConstant)
    (div_pos (P.eigenvalueBudget_pos ζ hζ) P.eigenvalueErrorConstant_pos)
  have hprod := mul_le_mul_of_nonneg_left hp P.eigenvalueErrorConstant_pos.le
  rw [mul_div_cancel₀ _ P.eigenvalueErrorConstant_pos.ne'] at hprod
  have hb : (P.eigenvalueErrorConstant : ℝ)*(1/2 : ℝ)^P.eigenvalueDigits ζ ≤
      (P.eigenvalueBudget ζ : ℝ) := by
    simpa only [eigenvalueDigits, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hprod
  apply he.trans
  apply le_trans (mul_le_mul_of_nonneg_right hconstant (by positivity))
  simpa only [one_div, inv_pow] using hb

def calibratedIncrement (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (ζ : ℚ) (hζ : 0 < ζ) (t : ℚ) :=
  P.roundedReciprocal ζ hζ (P.calibratedEigenvalue q ζ) t

theorem calibratedIncrement_spec (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (ζ : ℚ) (hζ : 0 < ζ) (t : ℚ)
    (ht : |(t : ℝ)| ≤ 1/(2*(P.incrementBound : ℝ))) :
    let ν := (P.calibratedIncrement q ζ hζ t).value
    0 < ν ∧ ν ≤ P.incrementBound ∧
      |(ν : ℝ)⁻¹-(P.eigenvalue+(t : ℝ))| ≤ (ζ : ℝ)^2 ∧
      Maxwell.rationalBitLength ν ≤ 4*ζ.den.size + P.reciprocalBitOverhead := by
  have hμ := P.calibratedEigenvalue_error q hqnorm hqerror ζ hζ
  have hv := P.roundedReciprocal_spec ζ hζ (P.calibratedEigenvalue q ζ) t hμ ht
  exact ⟨hv.1, hv.2.1, hv.2.2,
    P.roundedReciprocal_rationalBitLength ζ hζ (P.calibratedEigenvalue q ζ) t hμ ht⟩

end Maxwell.Composition.PhysicalPlatform
