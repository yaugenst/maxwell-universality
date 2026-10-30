import Maxwell.Continuum.CalibrationInterval
import Mathlib.Data.Rat.Cast.Lemmas

/-! The common source scale is computed by rational division of the
certified eigenvalue midpoint. Its error is checked entirely from the
rational enclosure endpoints. -/

namespace Maxwell.Continuum.FiniteAuxiliary

def sourceScalarApprox (α : ℚ) (I : Calibration.RationalInterval) : ℚ :=
  α / I.midpoint

def sourceScalarError (α : ℚ) (I : Calibration.RationalInterval) : ℚ :=
  α * I.width / (2 * I.lo ^ 2)

theorem sourceScalarApprox_error {α : ℚ} (hα : 0 ≤ α)
    (I : Calibration.RationalInterval) (hlo : 0 < I.lo)
    {μ : ℝ} (hμ : I.Contains μ) :
    |(sourceScalarApprox α I : ℝ) - (α : ℝ) / μ| ≤
      (sourceScalarError α I : ℝ) := by
  have hm : I.lo ≤ I.midpoint := by
    dsimp [Maxwell.Certificate.Interval.midpoint]
    linarith only [I.ordered]
  have hl : (0 : ℝ) < I.lo := by exact_mod_cast hlo
  have hmr : (I.lo : ℝ) ≤ I.midpoint := by exact_mod_cast hm
  have hmp := hl.trans_le hmr
  have hμp := hl.trans_le hμ.1
  have ha : (0 : ℝ) ≤ α := by exact_mod_cast hα
  have he := I.midpoint_error hμ
  have hw : (0 : ℝ) ≤ I.width := by exact_mod_cast I.width_nonneg
  have hden : (I.lo : ℝ)^2 ≤ (I.midpoint : ℝ)*μ := by
    simpa only [pow_two] using mul_le_mul hmr hμ.1 hl.le hmp.le
  have hi : |(I.midpoint : ℝ)⁻¹-μ⁻¹| ≤ (I.width : ℝ)/(2*(I.lo : ℝ)^2) := by
    rw [inv_sub_inv hmp.ne' hμp.ne', abs_div,
      abs_of_pos (mul_pos hmp hμp), abs_sub_comm]
    calc
      _ ≤ ((I.width : ℝ)/2)/((I.midpoint : ℝ)*μ) :=
        div_le_div_of_nonneg_right he (mul_pos hmp hμp).le
      _ ≤ ((I.width : ℝ)/2)/((I.lo : ℝ)^2) :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hl) hden
      _ = _ := by ring
  simp only [sourceScalarApprox, sourceScalarError, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_pow]
  calc
    _ = |(α : ℝ)*((I.midpoint : ℝ)⁻¹-μ⁻¹)| := by
      congr 1
      simp only [div_eq_mul_inv, mul_sub]
    _ = (α : ℝ)*|(I.midpoint : ℝ)⁻¹-μ⁻¹| := by rw [abs_mul, abs_of_nonneg ha]
    _ ≤ (α : ℝ)*((I.width : ℝ)/(2*(I.lo : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hi ha
    _ = _ := by ring

theorem sourceScalarApprox_tolerance {α ε : ℚ} (hα : 0 ≤ α)
    (I : Calibration.RationalInterval) (hlo : 0 < I.lo)
    {μ : ℝ} (hμ : I.Contains μ) (hcheck : sourceScalarError α I ≤ ε/16) :
    |(sourceScalarApprox α I : ℝ)-(α : ℝ)/μ| ≤ (ε : ℝ)/16 :=
  (sourceScalarApprox_error hα I hlo hμ).trans (by exact_mod_cast hcheck)

#print axioms sourceScalarApprox_error
#print axioms sourceScalarApprox_tolerance

end Maxwell.Continuum.FiniteAuxiliary
