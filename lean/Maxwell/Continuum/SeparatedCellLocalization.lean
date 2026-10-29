import Maxwell.Continuum.CellSpatialLocalization
import Maxwell.Continuum.SeparatedCellPolynomial

/-! Decay for the literal physical spatial restrictions of the separated
resolvent, obtained from the exact normalized cell kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch
open scoped InnerProduct

theorem spatialBlock_factor (T : FieldL2 →L[ℂ] FieldL2) (a b : Bloch.Alias) :
    (cellProjection a).comp (T.comp (cellProjection b)) =
      (1/8 : ℂ) • (embedLatticeCell a).comp
        ((((embedLatticeCell a)†).comp (T.comp (embedLatticeCell b))).comp
          (restrictLatticeCell b)) := by
  unfold cellProjection
  rw [restrictLatticeCell_eq_adjoint a]
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]

theorem spatialBlock_norm_le (T : FieldL2 →L[ℂ] FieldL2) (a b : Bloch.Alias) :
    ‖(cellProjection a).comp (T.comp (cellProjection b))‖ ≤
      ‖((embedLatticeCell a)†).comp (T.comp (embedLatticeCell b))‖ := by
  rw [spatialBlock_factor]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  rw [norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hb := (((embedLatticeCell a)†).comp (T.comp (embedLatticeCell b))).le_opNorm
    (restrictLatticeCell b f)
  have he := embedLatticeCell_norm_le a
    (((embedLatticeCell a)†) (T (embedLatticeCell b (restrictLatticeCell b f))))
  have hr := restrictLatticeCell_norm_le b f
  have hn := norm_nonneg (((embedLatticeCell a)†).comp (T.comp (embedLatticeCell b)))
  change ‖((embedLatticeCell a)†) (T (embedLatticeCell b (restrictLatticeCell b f)))‖ ≤ _ at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hr hn)
  nlinarith [mul_nonneg hn (norm_nonneg f)]

def separatedSpatialBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (cellProjection a).comp ((physicalSeparated D hσ0 hσ).comp (cellProjection b))

theorem separatedSpatialBlock_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖separatedSpatialBlock D hσ0 hσ a b‖ ≤ (2 : ℝ)^172 *
      Real.exp (-Real.sqrt (400 * ‖latticeShift b - latticeShift a‖ / (2 : ℝ)^157) / 64) :=
  (spatialBlock_norm_le (physicalSeparated D hσ0 hσ) a b).trans
    (separatedCellBlock_norm_le D hσ0 hσ a b)

theorem separatedSpatialBlock_polynomial {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (K : ℕ) :
    ‖latticeShift b - latticeShift a‖^K * ‖separatedSpatialBlock D hσ0 hσ a b‖ ≤
      (2 : ℝ)^170 * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2 :=
  (mul_le_mul_of_nonneg_left (spatialBlock_norm_le (physicalSeparated D hσ0 hσ) a b)
    (by positivity)).trans (separatedCellBlock_polynomial D hσ0 hσ a b K)

theorem separatedSpatialBlock_order16 {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖latticeShift b - latticeShift a‖^16 * ‖separatedSpatialBlock D hσ0 hσ a b‖ ≤
      (2 : ℝ)^2810 :=
  (mul_le_mul_of_nonneg_left (spatialBlock_norm_le (physicalSeparated D hσ0 hσ) a b)
    (by positivity)).trans (separatedCellBlock_order16 D hσ0 hσ a b)

#print axioms spatialBlock_norm_le
#print axioms separatedSpatialBlock_norm_le
#print axioms separatedSpatialBlock_order16

end Maxwell.Continuum.CellGauge
