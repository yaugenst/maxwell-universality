import Maxwell.Green.CalibrationBudget
import Maxwell.Realization.ScalarPrecision

/-! Exact rational reciprocal tuning and final dyadic scalar-cell output.
The spectral quantity is approximated once; every diagonal letter uses the
same approximation and actual reciprocal arithmetic. -/
namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Green.PhysicalCompression
open scoped InnerProductSpace
set_option maxHeartbeats 600000

theorem eigenvalue_abs_le (P : PhysicalPlatform) : |P.eigenvalue| ≤ 1 / (P.bulkGap : ℝ) := by
  have he : inner ℝ P.mode
      (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0 P.mode) = P.eigenvalue := by
    rw [P.mode_equation, inner_smul_right, real_inner_self_eq_norm_sq, P.mode_unit]
    simp
  rw [← he, ← P.scalarCoupling_weightedMode]
  apply (Complex.abs_re_le_norm _).trans
  rw [← offdiagonalCompression_inner]
  let x := realCoordinateEmbedding P.weightedMode
  let R := offdiagonalCompression (ScalarDefect.edgeEmbedding P.defect)
    (P.bulk.symm : Field →L[ℂ] Field) 0
  have hx : ‖x‖ ≤ 1 := by rw [realCoordinateEmbedding.norm_map]; exact P.weightedMode_norm_le
  have hR : ‖R‖ ≤ 1 / (P.bulkGap : ℝ) :=
    (offdiagonalCompression_norm_le _ _ _).trans P.bulk_inverse_bound
  have hgp : 0 ≤ 1 / (P.bulkGap : ℝ) := by
    exact (one_div_pos.mpr (by exact_mod_cast P.bulkGap_pos)).le
  change ‖inner ℂ x (R x)‖ ≤ _
  calc
    _ ≤ ‖x‖ * ‖R x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖R‖ * ‖x‖) := mul_le_mul_of_nonneg_left (R.le_opNorm x) (norm_nonneg _)
    _ ≤ 1 * ((1 / (P.bulkGap : ℝ)) * 1) := by gcongr
    _ = _ := by ring

def reciprocalLower (P : PhysicalPlatform) : ℚ :=
  (1/P.bulkGap + 1/P.incrementBound)⁻¹

theorem reciprocalLower_pos (P : PhysicalPlatform) : 0 < P.reciprocalLower := by
  have := P.bulkGap_pos
  have := P.incrementBound_pos
  unfold reciprocalLower
  positivity

def calibratedReciprocal (μhat t : ℚ) : ℚ := (μhat+t)⁻¹

/-- The exact rational reciprocal has a fixed positive floor and leaves
room for the final dyadic rounding inside the permitted scalar increment. -/
theorem calibratedReciprocal_bounds (P : PhysicalPlatform) (μhat t : ℚ) (ε : ℝ)
    (hμ : |(μhat : ℝ)-P.eigenvalue| ≤ ε)
    (hε : ε ≤ 1/(4*(P.incrementBound : ℝ)))
    (ht : |(t : ℝ)| ≤ 1/(2*(P.incrementBound : ℝ))) :
    P.reciprocalLower ≤ calibratedReciprocal μhat t ∧
      calibratedReciprocal μhat t ≤ (4/5)*P.incrementBound := by
  have hv : 0 < (P.incrementBound : ℝ) := by exact_mod_cast P.incrementBound_pos
  have hg : 0 < (P.bulkGap : ℝ) := by exact_mod_cast P.bulkGap_pos
  have hμlo := (abs_le.mp hμ).1
  have hμhi := (abs_le.mp hμ).2
  have htlo := (abs_le.mp ht).1
  have hthi := (abs_le.mp ht).2
  have hlower : 5 / (4*(P.incrementBound : ℝ)) ≤ (μhat : ℝ)+t := by
    have hh := P.eigenvalue_headroom
    have hfour : 2/(P.incrementBound : ℝ) - 1/(4*(P.incrementBound : ℝ)) -
        1/(2*(P.incrementBound : ℝ)) = 5/(4*(P.incrementBound : ℝ)) := by field_simp; ring
    linarith
  have hpos : 0 < (μhat : ℝ)+t := (div_pos (by norm_num) (mul_pos (by norm_num) hv)).trans_le hlower
  have hupper : (μhat : ℝ)+t ≤ 1/(P.bulkGap : ℝ)+1/(P.incrementBound : ℝ) := by
    have hμnorm := (le_abs_self P.eigenvalue).trans P.eigenvalue_abs_le
    have hfrac : 1/(4*(P.incrementBound : ℝ)) + 1/(2*(P.incrementBound : ℝ)) ≤
        1/(P.incrementBound : ℝ) := by
      have hid : 1/(4*(P.incrementBound : ℝ)) + 1/(2*(P.incrementBound : ℝ)) =
          (3/4 : ℝ) * (1/(P.incrementBound : ℝ)) := by field_simp; ring
      rw [hid]
      nlinarith [one_div_pos.mpr hv]
    linarith
  have hlo : (1/(P.bulkGap : ℝ)+1/(P.incrementBound : ℝ))⁻¹ ≤
      ((μhat : ℝ)+t)⁻¹ := inv_anti₀ hpos hupper
  have hhi : ((μhat : ℝ)+t)⁻¹ ≤ (4/5 : ℝ)*(P.incrementBound : ℝ) := by
    have h := inv_anti₀ (div_pos (by norm_num) (mul_pos (by norm_num) hv)) hlower
    convert h using 1; field_simp
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [reciprocalLower, calibratedReciprocal, Rat.cast_inv, Rat.cast_add,
      Rat.cast_div, Rat.cast_one] using hlo
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [calibratedReciprocal, Rat.cast_inv, Rat.cast_add, Rat.cast_mul,
      Rat.cast_div, Rat.cast_ofNat] using hhi

theorem calibratedReciprocal_error (μhat t : ℚ) (μ ε : ℝ)
    (hμ : |(μhat : ℝ)-μ| ≤ ε) :
    |(calibratedReciprocal μhat t : ℝ)⁻¹-(μ+(t : ℝ))| ≤ ε := by
  simpa only [calibratedReciprocal, Rat.cast_inv, Rat.cast_add, inv_inv,
    add_sub_add_right_eq_sub] using hμ

def eigenvalueBudget (P : PhysicalPlatform) (ζ : ℚ) : ℚ :=
  min (ζ^2/2) (1/(4*P.incrementBound))

theorem eigenvalueBudget_pos (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ) :
    0 < P.eigenvalueBudget ζ := by
  have := P.incrementBound_pos
  unfold eigenvalueBudget
  positivity

def roundedReciprocal (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ) (μhat t : ℚ) :=
  Realization.scalarRound P.reciprocalLower ζ (P.incrementBound/8)
    P.reciprocalLower_pos hζ (div_pos P.incrementBound_pos (by norm_num))
    (calibratedReciprocal μhat t)

/-- Positivity, material increment cap and the complete real spectral
reciprocal error hold for the actual emitted dyadic scalar. -/
theorem roundedReciprocal_spec (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ) (μhat t : ℚ)
    (hμ : |(μhat : ℝ)-P.eigenvalue| ≤ (P.eigenvalueBudget ζ : ℝ))
    (ht : |(t : ℝ)| ≤ 1/(2*(P.incrementBound : ℝ))) :
    let ν := (P.roundedReciprocal ζ hζ μhat t).value
    0 < ν ∧ ν ≤ P.incrementBound ∧
      |(ν : ℝ)⁻¹-(P.eigenvalue+(t : ℝ))| ≤ (ζ : ℝ)^2 := by
  dsimp only
  have hsmall : (P.eigenvalueBudget ζ : ℝ) ≤ 1/(4*(P.incrementBound : ℝ)) := by
    have h : P.eigenvalueBudget ζ ≤ 1/(4*P.incrementBound) := min_le_right _ _
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr h
  have hhalf : (P.eigenvalueBudget ζ : ℝ) ≤ (ζ : ℝ)^2/2 := by
    have h : P.eigenvalueBudget ζ ≤ ζ^2/2 := min_le_left _ _
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr h
  have hb := P.calibratedReciprocal_bounds μhat t (P.eigenvalueBudget ζ) hμ hsmall ht
  have hr := Realization.scalarRound_bounds P.reciprocalLower ζ (P.incrementBound/8)
    P.reciprocalLower_pos hζ (div_pos P.incrementBound_pos (by norm_num))
    (calibratedReciprocal μhat t) hb.1
  refine ⟨hr.1, ?_, ?_⟩
  · have hh := (abs_le.mp hr.2.1).2
    change (P.roundedReciprocal ζ hζ μhat t).value ≤ P.incrementBound
    have hp := P.incrementBound_pos
    change (P.roundedReciprocal ζ hζ μhat t).value - calibratedReciprocal μhat t ≤
      P.incrementBound/8 at hh
    linarith [hb.2]
  · exact Realization.scalarRound_tuning_real P.reciprocalLower ζ (P.incrementBound/8)
      P.reciprocalLower_pos hζ (div_pos P.incrementBound_pos (by norm_num))
      (calibratedReciprocal μhat t) (P.eigenvalue+(t : ℝ)) hb.1
      ((calibratedReciprocal_error μhat t P.eigenvalue _ hμ).trans hhalf)

/-- The rounded calibration is installed as a uniform scalar-cell increment;
its full remaining reserve is expressed in the original scalar material units. -/
theorem roundedReciprocal_material (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ)
    (μhat t : ℚ)
    (hμ : |(μhat : ℝ)-P.eigenvalue| ≤ (P.eigenvalueBudget ζ : ℝ))
    (ht : |(t : ℝ)| ≤ 1/(2*(P.incrementBound : ℝ))) (c : Cell20) :
    let ν := (P.roundedReciprocal ζ hζ μhat t).value
    1 ≤ P.background.material c + 64*ν ∧
      P.background.material c + 64*ν ≤ 25-64*P.incrementBound := by
  have hv := P.roundedReciprocal_spec ζ hζ μhat t hμ ht
  have hb := P.background.bounds c
  have hr := P.increment_reserve
  dsimp only at hv ⊢
  constructor <;> linarith [hv.1, hv.2.1, hb.1, hb.2]

end Maxwell.Composition.PhysicalPlatform
