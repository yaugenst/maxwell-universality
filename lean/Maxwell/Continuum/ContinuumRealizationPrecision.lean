import Maxwell.Continuum.ContinuumRealizationMaterial
import Maxwell.Continuum.FiniteAuxiliarySourceScalar

/-! Finite scalar checks for the selected continuum output. Positivity
of the eigenvalue interval and reciprocal stability are consequences of
the actual defect spectrum, rather than extra calibration promises. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Auxiliary EffectiveMass FiniteAuxiliary
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput muH

namespace Enclosures

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0 < S.nnz}
variable (C : Enclosures p S hm)

theorem mode_lower_ge_one : 1 ≤ C.mode.lo := by
  have hμ := (muH_bounds (energyCalibration p S hm)
    (inverse_length_le_1024 (length_master p S hm))).1
  simp only [inv_pow, inv_inv] at hμ
  have hL : (2 : ℝ)^65 ≤ length p S hm :=
    (power_le_Ls (by have := exponent_large; omega)).trans (length_master p S hm)
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2^65) hL 2
  have hlow := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 1/2^128 by positivity)
  have hfour : (4 : ℝ) ≤ muH (energyCalibration p S hm)
      (inverse_length_le_1024 (length_master p S hm)) := by
    rw [show (1/(2 : ℝ)^128)*((2 : ℝ)^65)^2 = 4 by norm_num] at hlow
    exact hlow.trans hμ
  have hwidth : C.mode.width ≤ 1/8 := by
    have hz : (zeta p S hm)^2 ≤ 1 := pow_le_one₀ (zeta_pos p S hm).le (zeta_le_one p S hm)
    exact C.mode_width.trans (by linarith only [hz])
  have hwR : (C.mode.hi : ℝ)-(C.mode.lo : ℝ) ≤ 1/8 := by
    change C.mode.hi-C.mode.lo ≤ 1/8 at hwidth
    have hh := Rat.cast_le (K := ℝ) |>.mpr hwidth
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have hc := C.mode_contains.2
  have hlo : (1 : ℝ) ≤ C.mode.lo := by linarith only [hfour, hwR, hc]
  exact_mod_cast hlo

def sourceScalar : ℚ := sourceScalarApprox (alpha p S hm) C.mode

theorem sourceScalarError_le_width : sourceScalarError (alpha p S hm) C.mode ≤ C.mode.width/2 := by
  have hα1 : alpha p S hm ≤ 1 := by exact_mod_cast (spacing_bounds p S hm).2.2.1
  have hw := C.mode.width_nonneg
  have hl := C.mode_lower_ge_one
  have hsq : (1 : ℚ) ≤ C.mode.lo^2 := one_le_pow₀ hl
  have hαw := mul_le_mul_of_nonneg_right hα1 hw
  have hwlo := mul_le_mul_of_nonneg_left hsq hw
  unfold sourceScalarError
  apply (div_le_iff₀ (show (0 : ℚ) < 2*C.mode.lo^2 by positivity)).mpr
  nlinarith only [hαw, hwlo]

theorem sourceScalar_error :
    |(C.sourceScalar : ℝ)-(alpha p S hm : ℝ)/
      muH (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))| ≤
        (C.mode.width : ℝ)/2 := by
  have he := sourceScalarApprox_error
    (by exact_mod_cast (alpha_pos p S hm).le : 0 ≤ alpha p S hm)
    C.mode (zero_lt_one.trans_le C.mode_lower_ge_one) C.mode_contains
  exact he.trans (by exact_mod_cast C.sourceScalarError_le_width)

theorem sourceScalar_tolerance {ef : ℝ} (hw : (C.mode.width : ℝ) ≤ ef/8) :
    |(C.sourceScalar : ℝ)-(alpha p S hm : ℝ)/
      muH (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))| ≤ ef/16 :=
  C.sourceScalar_error.trans (by linarith only [hw])

end Enclosures

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

theorem material_error_weighted (N : ℕ) :
    Enclosures.materialError p S hm N*
      ((2 : ℝ)^142*(budget p S hm : ℝ)*(length p S hm : ℝ)^2) =
      3*(2 : ℝ)^272*(budget p S hm : ℝ)*(1/2 : ℝ)^(N+24) := by
  have hL : (length p S hm : ℝ) ≠ 0 := by exact_mod_cast (length_pos p S hm).ne'
  calc
    _ = 3*((2 : ℝ)^130*(2 : ℝ)^142)*(budget p S hm : ℝ)*
        ((length p S hm : ℝ)⁻¹^2*(length p S hm : ℝ)^2)*(1/2 : ℝ)^(N+24) := by
      unfold Enclosures.materialError
      ring
    _ = _ := by
      rw [← pow_add, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hL), mul_one]

#print axioms Enclosures.mode_lower_ge_one
#print axioms Enclosures.sourceScalar_tolerance
#print axioms material_error_weighted

end Maxwell.Continuum.RealizationParameters
