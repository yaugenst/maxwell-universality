import Maxwell.Continuum.CalibrationPeriodizationPrecision
import Maxwell.Continuum.EffectiveMassAuxiliaryTranslation

/-! The all-image approximation of the literal broad-well auxiliary
operator, on its original physical L² space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge EffectiveMass MasterConstants

attribute [local irreducible] Auxiliary.resolvent Sh Qh

theorem twoWellCells_zero (L : ℝ) : twoWellCells L (0 : Bloch.Alias) = ballCells L := by
  classical
  simp [twoWellCells, wellCells]

theorem imageRadius_zero : imageRadius (0 : Bloch.Alias) = 0 := by simp [imageRadius]

def periodizedAuxiliary {L z : ℝ} (D : Auxiliary.Calibration L⁻¹ z) (M : ℕ) :
    FieldL2 →L[ℂ] FieldL2 :=
  Qh L⁻¹ * periodizedCompression D le_rfl (by positivity) M (ballCells L) (ballCells L) * Qh L⁻¹

theorem auxiliary_cell_compression {L z : ℝ} (hL : 0 < L) (D : Auxiliary.Calibration L⁻¹ z) :
    Qh L⁻¹ * ((familyProjection (ballCells L)).comp
      ((resolvent D le_rfl (by positivity)).comp (familyProjection (ballCells L)))) * Qh L⁻¹ = Sh D := by
  rw [Sh]
  apply ContinuousLinearMap.ext
  intro f
  change Qh L⁻¹ (familyProjection (ballCells L) (resolvent D le_rfl (by positivity)
    (familyProjection (ballCells L) (Qh L⁻¹ f)))) = Qh L⁻¹ (resolvent D le_rfl (by positivity) (Qh L⁻¹ f))
  have hi := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (familyProjection_Qh hL)
  change familyProjection (ballCells L) (Qh L⁻¹ f) = Qh L⁻¹ f at hi
  rw [hi]
  exact congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T (resolvent D le_rfl (by positivity) (Qh L⁻¹ f)))
    (Qh_familyProjection hL)

theorem periodizedAuxiliary_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (M : ℕ) (hM : 16*(L+1) ≤ (M : ℝ)) :
    ‖periodizedAuxiliary D M-Sh D‖ ≤ Cs^2*L^10*Real.exp (-(cs/8)*Real.sqrt (M/L)) := by
  have hb := twoWell_periodization_error hL D le_rfl (by positivity) (0 : Bloch.Alias) M
    (by simpa only [imageRadius_zero, Nat.cast_zero, add_zero] using hM)
  rw [twoWellCells_zero] at hb
  let P := (familyProjection (ballCells L)).comp
    ((resolvent D le_rfl (by positivity)).comp (familyProjection (ballCells L)))
  let A := periodizedCompression D le_rfl (by positivity) M (ballCells L) (ballCells L)
  have he : periodizedAuxiliary D M-Sh D = Qh L⁻¹*(A-P)*Qh L⁻¹ := by
    rw [← auxiliary_cell_compression (length_pos hL) D]
    change Qh L⁻¹*A*Qh L⁻¹-Qh L⁻¹*P*Qh L⁻¹ = _
    rw [mul_sub, sub_mul]
  rw [he]
  calc
    _ ≤ ‖Qh L⁻¹‖*‖A-P‖*‖Qh L⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖A-P‖*1 := by gcongr <;> exact Qh_norm_le L⁻¹
    _ = ‖A-P‖ := by ring
    _ ≤ _ := hb

theorem periodizedAuxiliary_requested_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (M N ell : ℕ) (hM : 16*(L+1) ≤ (M : ℝ))
    (hlog : L ≤ (2 : ℝ)^ell)
    (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2 ≤ (M : ℝ)) :
    ‖periodizedAuxiliary D M-Sh D‖ ≤ (1/2 : ℝ)^(N+20) :=
  (periodizedAuxiliary_error hL D M hM).trans
    (periodization_error_budget (length_pos hL) N ell hlog hsize)

#print axioms periodizedAuxiliary_requested_error

end Maxwell.Continuum.Calibration
