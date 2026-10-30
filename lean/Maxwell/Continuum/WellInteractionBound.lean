import Maxwell.Continuum.FullCellBounds
import Maxwell.Continuum.CellSpatialSchur
import Maxwell.Continuum.CellHessianMetric

/-! Full physical interactions between the literal radius-L wells.
The finite spatial cover and its orthogonality recover the L^5
prefactor from the actual cell resolvent bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary CellGauge Bloch PeriodicBand MasterConstants

def wellInteraction {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (k : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (Qh h).comp ((resolvent D hσ0 hσ).comp
    ((translationOperator (-latticeShift k)).comp (Qh h)))

theorem wellInteraction_factor {L z σ : ℝ} (hL : 0 < L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64) (k : Bloch.Alias) :
    wellInteraction D hσ0 hσ k =
      (Qh L⁻¹).comp (((familyProjection (ballCells L)).comp
        ((resolvent D hσ0 hσ).comp (familyProjection (wellCells L k)))).comp
          ((translationOperator (-latticeShift k)).comp (Qh L⁻¹))) := by
  apply ContinuousLinearMap.ext
  intro f
  change Qh L⁻¹ (resolvent D hσ0 hσ (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))) =
    Qh L⁻¹ (familyProjection (ballCells L) (resolvent D hσ0 hσ
      (familyProjection (wellCells L k) (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))))
  rw [familyProjection_translatedQh hL]
  exact (congrArg (fun T : FieldL2 →L[ℂ] FieldL2 =>
    T (resolvent D hσ0 hσ (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))))
    (Qh_familyProjection hL)).symm

theorem wellInteraction_norm_le_cover {L z σ : ℝ} (hL : 0 < L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64) (k : Bloch.Alias) :
    ‖wellInteraction D hσ0 hσ k‖ ≤
      ‖(familyProjection (ballCells L)).comp
        ((resolvent D hσ0 hσ).comp (familyProjection (wellCells L k)))‖ := by
  rw [wellInteraction_factor hL]
  let T := (familyProjection (ballCells L)).comp
    ((resolvent D hσ0 hσ).comp (familyProjection (wellCells L k)))
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖Qh L⁻¹ (T (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))‖ ≤ ‖T‖ * ‖f‖
  calc
    _ ≤ ‖T (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))‖ := by
      simpa only [one_mul] using (Qh L⁻¹).le_of_opNorm_le (Qh_norm_le L⁻¹)
        (T (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))
    _ ≤ ‖T‖ * ‖fieldTranslation (-latticeShift k) (Qh L⁻¹ f)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖f‖ := by
      rw [(fieldTranslation (-latticeShift k)).norm_map]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [one_mul] using (Qh L⁻¹).le_of_opNorm_le (Qh_norm_le L⁻¹) f

theorem wellInteraction_exponential {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64) (k : Bloch.Alias) :
    ‖wellInteraction D hσ0 hσ k‖ ≤ (2 : ℝ)^175 * L^5 *
      (Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp) + Real.exp (-cs*L)) := by
  let E := Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp)
  let e := Real.exp (-cs*L)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hlarge := length_ge_one hL
  have hblock : ∀ a ∈ ballCells L, ∀ b ∈ wellCells L k,
      ‖(cellProjection a).comp ((resolvent D hσ0 hσ).comp (cellProjection b))‖ ≤
        (2 : ℝ)^165 * L^2 * (E+e) := by
    intro a ha b hb
    have hb₀ := resolventSpatialBlock_exponential hL D hσ0 hσ a b
    have he₀ := wellCells_exponential_le hlarge k ha hb
    change ‖(cellProjection a).comp ((resolvent D hσ0 hσ).comp (cellProjection b))‖ ≤ _ at hb₀
    apply hb₀.trans
    calc
      _ ≤ (2 : ℝ)^69 * L^2 * ((2 : ℝ)^96 * E + e) := by gcongr
      _ ≤ (2 : ℝ)^69 * L^2 * ((2 : ℝ)^96 * E + (2 : ℝ)^96 * e) := by
        gcongr
        exact le_mul_of_one_le_left he (by norm_num)
      _ = (2 : ℝ)^165 * L^2 * (E+e) := by ring
  have hb := family_block_norm_le_count (ballCells L) (wellCells L k) (resolvent D hσ0 hσ)
    (M := (2 : ℝ)^165 * L^2 * (E+e)) (N := (2 : ℝ)^10 * L^3)
    (by positivity) (by positivity) (ballCells_card_le hlarge) (wellCells_card_le hlarge k) hblock
  apply (wellInteraction_norm_le_cover (length_pos hL) D hσ0 hσ k).trans (hb.trans_eq _)
  change ((2 : ℝ)^165 * L^2 * (E+e)) * ((2 : ℝ)^10 * L^3) = (2 : ℝ)^175 * L^5 * (E+e)
  ring

theorem wellInteraction_exponential_master {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64) (k : Bloch.Alias) :
    ‖wellInteraction D hσ0 hσ k‖ ≤ Cs * L^5 *
      (Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp) + Real.exp (-cs*L)) := by
  apply (wellInteraction_exponential hL D hσ0 hσ k).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (length_pos hL).le 5)
  exact fixed_power_le_Cs (by have := exponent_large; omega)

#print axioms wellInteraction_factor
#print axioms wellInteraction_exponential_master

end Maxwell.Continuum.EffectiveMass
