import Maxwell.Green.CalibrationBudget

/-! The three computed axial calibration values inherit the actual full
Green upper bound and the signed-mediator lower bound. -/
namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Green.PhysicalCompression
open scoped InnerProductSpace
set_option maxHeartbeats 600000

theorem physical_mode_coupling_norm_le (P : PhysicalPlatform) (n : Site) :
    |inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode)| ≤
    ‖weightedBlock (ScalarDefect.edgeEmbedding P.defect) (ScalarDefect.coordinateWeight P.defect)
      (P.bulk.symm : Field →L[ℂ] Field) n‖ := by
  let R := physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n
  calc
    _ = ‖inner ℝ P.mode (R P.mode)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖P.mode‖ * ‖R P.mode‖ := norm_inner_le_norm _ _
    _ ≤ ‖P.mode‖ * (‖R‖ * ‖P.mode‖) :=
      mul_le_mul_of_nonneg_left (R.le_opNorm _) (norm_nonneg _)
    _ = ‖R‖ := by rw [P.mode_unit]; ring
    _ ≤ _ := realPartOperator_norm_le _

theorem physical_mode_axial_upper (P : PhysicalPlatform) (d : ℕ)
    (hd : P.spacing.minimumDistance ≤ d) (j : Direction) :
    |inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
      ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode)| ≤
      (P.greenConstant : ℝ) * (P.spacing.zeta d : ℝ) := by
  apply (P.physical_mode_coupling_norm_le _).trans
  have hj : unitSite j ≠ 0 := by
    intro h
    have hh := congrFun h j
    simp [unitSite] at hh
  have hg := P.green_upper d hd (unitSite j) hj
  have hlen : Realization.latticeLength (unitSite j) = 1 := by
    simp only [Realization.latticeLength, unitSite, Pi.single_apply]
    simp_rw [apply_ite Int.natAbs]
    simp
  simpa only [hlen, pow_one, Realization.SpacingPlatform.zeta, Rat.cast_pow] using hg

theorem signedCoupling_axial_upper (P : PhysicalPlatform)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ)
    (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) :
    |(P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) : ℝ)| ≤
      (P.greenConstant : ℝ) * (P.spacing.zeta d : ℝ) + (P.spacing.zeta d : ℝ)^2 := by
  have he := (P.signedCoupling_axial (P.spacing.zeta d) (P.spacing.zeta_pos d) d hd j a ha).1
  have hg := P.physical_mode_axial_upper d hd j
  have ht := abs_sub_le
    (P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) : ℝ)
    (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
      ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode)) 0
  simp only [sub_zero, abs_neg] at ht
  linarith

theorem signedCoupling_axial_three_alpha (P : PhysicalPlatform)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ)
    (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d))
    (hζ : (P.spacing.zeta d)^2 ≤ P.spacing.alpha d) :
    3*(P.spacing.alpha d : ℝ) ≤
      |(P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
        (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) : ℝ)| := by
  have he := (P.signedCoupling_axial (P.spacing.zeta d) (P.spacing.zeta_pos d) d hd j a ha).1
  have hg := P.green_axial d hd j
  have hz : (P.spacing.zeta d : ℝ)^2 ≤ (P.spacing.alpha d : ℝ) := by
    simpa only [Rat.cast_pow] using (Rat.cast_le (K := ℝ)).mpr hζ
  have halpha : 4*(P.spacing.alpha d : ℝ) =
      (P.spacing.c : ℝ)*(P.spacing.a : ℝ)^d := by
    simp only [Realization.SpacingPlatform.alpha, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_pow]
    ring
  have ht := abs_abs_sub_abs_le_abs_sub
    (P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) : ℝ)
    (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
      ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode))
  rw [abs_neg] at ht
  have hl := (abs_le.mp (ht.trans he)).1
  linarith

end Maxwell.Composition.PhysicalPlatform
