import Maxwell.Green.CouplingCalibration

/-! The calibration output approximates the same selected physical mode
and its actual translated weighted Green blocks. -/
namespace Maxwell.Green
open scoped InnerProductSpace

/-- Quadratic readout stability, without a symmetry assumption. -/
theorem quadratic_readout_difference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (R : E →L[ℂ] E) (x y : E) :
    ‖inner ℂ x (R x) - inner ℂ y (R y)‖ ≤
      ‖R‖ * ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have hid : inner ℂ x (R x) - inner ℂ y (R y) =
      inner ℂ (x - y) (R x) + inner ℂ y (R (x - y)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    abel
  rw [hid]
  calc
    _ ≤ ‖inner ℂ (x-y) (R x)‖ + ‖inner ℂ y (R (x-y))‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ * ‖R x‖ + ‖y‖ * ‖R (x-y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x-y‖ * (‖R‖ * ‖x‖) + ‖y‖ * (‖R‖ * ‖x-y‖) := by
      gcongr
      · exact R.le_opNorm x
      · exact R.le_opNorm (x-y)
    _ = _ := by ring

end Maxwell.Green

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression
open scoped InnerProductSpace
set_option maxHeartbeats 600000

noncomputable def rationalCoordinates {N : ℕ} (a : Fin N → ℚ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => (a i : ℝ))

theorem weightedMode_norm_le (P : PhysicalPlatform) : ‖P.weightedMode‖ ≤ 1 := by
  have hD : ‖sqrtWeightOperator (ScalarDefect.coordinateWeight P.defect)‖ ≤ 1 := by
    apply weight_diagonal_norm_le _ 1 zero_le_one
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hw := ScalarDefect.coordinateWeight_bounds P.defect i
    have h0 : (0 : ℝ) ≤ ScalarDefect.coordinateWeight P.defect i := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1/4) hw.1)
    have h1 : (ScalarDefect.coordinateWeight P.defect i : ℝ) ≤ 1 := by exact_mod_cast hw.2
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (ScalarDefect.coordinateWeight P.defect i : ℝ)]
  calc
    ‖P.weightedMode‖ ≤ ‖sqrtWeightOperator (ScalarDefect.coordinateWeight P.defect)‖ * ‖P.mode‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 := by rw [P.mode_unit, mul_one]; exact hD

theorem scalarCoupling_weightedMode (P : PhysicalPlatform) (n : Site) :
    (scalarCoupling (ScalarDefect.edgeEmbedding P.defect) (realCoordinateEmbedding P.weightedMode)
      (P.bulk.symm : Field →L[ℂ] Field) n).re =
    inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode) := by
  unfold physicalGreenBlock
  rw [realPartOperator_apply, realCoordinatePart_inner_right, weightedBlock_inner,
    complexSqrtWeightOperator_embedding]
  rfl

/-- A single exact rational evaluator serves every translation and every
requested binary precision. Only the rational source vector is input data. -/
theorem rationalCoupling_mode_error (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (b : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤ ε) :
    |(P.rationalCoupling (ScalarDefect.edgeEmbedding P.defect) a n b : ℝ) -
      inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode)| ≤
      (1 / 2 : ℝ)^b * (1 + ε)^2 + (1 / (P.bulkGap : ℝ)) * ε * (2 + ε) := by
  let x := realCoordinateEmbedding (rationalCoordinates a)
  let y := realCoordinateEmbedding P.weightedMode
  let R := offdiagonalCompression (ScalarDefect.edgeEmbedding P.defect)
    (P.bulk.symm : Field →L[ℂ] Field) n
  have hx : ‖x‖ ≤ 1 + ε := by
    rw [realCoordinateEmbedding.norm_map]
    have ht := norm_add_le (rationalCoordinates a - P.weightedMode) P.weightedMode
    rw [sub_add_cancel] at ht
    linarith [P.weightedMode_norm_le]
  have hy : ‖y‖ ≤ 1 := by
    rw [realCoordinateEmbedding.norm_map]
    exact P.weightedMode_norm_le
  have hxy : ‖x-y‖ ≤ ε := by
    change ‖realCoordinateEmbedding (rationalCoordinates a) - realCoordinateEmbedding P.weightedMode‖ ≤ ε
    rw [← map_sub, realCoordinateEmbedding.norm_map]
    exact ha
  have hR : ‖R‖ ≤ 1 / (P.bulkGap : ℝ) :=
    (offdiagonalCompression_norm_le _ _ _).trans P.bulk_inverse_bound
  have hb := P.rationalCoupling_error (ScalarDefect.edgeEmbedding P.defect) a n b
  have hcoords : WithLp.toLp 2 (fun i => (a i : ℂ)) = x := by
    ext i
    simp [x, rationalCoordinates]
  have hf : (fun i => (a i : ℂ)) = (x : _ → ℂ) := by
    funext i
    simp [x, rationalCoordinates]
  rw [hcoords, hf, ← offdiagonalCompression_inner] at hb
  have hd := Maxwell.Green.quadratic_readout_difference R x y
  have hd' : ‖inner ℂ x (R x) - inner ℂ y (R y)‖ ≤
      (1 / (P.bulkGap : ℝ)) * ε * (2+ε) := by
    apply hd.trans
    have hg : 0 ≤ 1 / (P.bulkGap : ℝ) := by exact le_of_lt (one_div_pos.mpr (by exact_mod_cast P.bulkGap_pos))
    exact mul_le_mul (mul_le_mul hR hxy (norm_nonneg _) hg)
      (by linarith : ‖x‖ + ‖y‖ ≤ 2 + ε) (by positivity) (by positivity)
  have hb' : ‖(P.rationalCoupling (ScalarDefect.edgeEmbedding P.defect) a n b : ℂ) -
      inner ℂ x (R x)‖ ≤ (1/2 : ℝ)^b * (1+ε)^2 := by
    apply hb.trans
    gcongr
  have hs := (norm_add_le
    ((P.rationalCoupling (ScalarDefect.edgeEmbedding P.defect) a n b : ℂ) - inner ℂ x (R x))
    (inner ℂ x (R x) - inner ℂ y (R y))).trans (add_le_add hb' hd')
  rw [sub_add_sub_cancel] at hs
  have hre := (Complex.abs_re_le_norm
    ((P.rationalCoupling (ScalarDefect.edgeEmbedding P.defect) a n b : ℂ) - inner ℂ y (R y))).trans hs
  rw [Complex.sub_re, Complex.ratCast_re, offdiagonalCompression_inner,
    scalarCoupling_weightedMode] at hre
  exact hre

/-- The sign required for the calibrated axial bond is applied by exact
rational negation, preserving the proved error. -/
def signedCoupling (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (b : ℕ) : ℚ :=
  -P.rationalCoupling (ScalarDefect.edgeEmbedding P.defect) a n b

theorem signedCoupling_mode_error (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (b : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤ ε) :
    |(P.signedCoupling a n b : ℝ) -
      (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode))| ≤
      (1 / 2 : ℝ)^b * (1 + ε)^2 + (1 / (P.bulkGap : ℝ)) * ε * (2 + ε) := by
  simpa only [signedCoupling, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using
    P.rationalCoupling_mode_error a n b ε hε ha

end Maxwell.Composition.PhysicalPlatform
