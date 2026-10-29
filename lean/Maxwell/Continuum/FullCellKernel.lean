import Maxwell.Continuum.FullCellPairing
import Maxwell.Continuum.SeparatedCellLocalization

/-! The exact operator Fourier kernel and literal spatial restriction of
the complete physical cutoff resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber Auxiliary Bloch OperatorFourier MeasureTheory Set Metric
open scoped InnerProduct

local instance : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] fullFiberResolvent cutoffFullCellSymbol Auxiliary.resolvent embedLatticeCell

theorem resolvent_fourier_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (resolvent D hσ0 hσ (embedLatticeCell b f)) =
      ((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b) *
        inner ℂ g (angularFourier (cutoffFullCellSymbol z σ) (latticeShift b - latticeShift a) f) := by
  rw [resolvent_cell_pairing D hσ0 hσ]
  simp_rw [latticePhase_ratio]
  have he : (∫ q : QuasiCell, (carrier (latticeShift a - latticeShift b) *
      Complex.exp ((-inner ℝ q.val (latticeShift b - latticeShift a) : ℝ) * Complex.I)) *
        inner ℂ g (cutoffFullCellSymbol z σ q.val f) ∂quasiMeasure) =
      carrier (latticeShift a - latticeShift b) *
        ∫ q : QuasiCell, angularPhase q.val (latticeShift b - latticeShift a) *
          inner ℂ g (cutoffFullCellSymbol z σ q.val f) ∂quasiMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by unfold angularPhase; ring
  have hz (q : Space) (hq : q ∉ quasiCell) :
      angularPhase q (latticeShift b - latticeShift a) *
        inner ℂ g (cutoffFullCellSymbol z σ q f) = 0 := by
    rw [cutoffFullCellSymbol_zero_outside z σ hq, zero_apply, inner_zero_right, mul_zero]
  have hqi := quasi_integral_supported
    (fun q : Space => angularPhase q (latticeShift b - latticeShift a) *
      inner ℂ g (cutoffFullCellSymbol z σ q f)) hz
  rw [he, hqi, ← angularFourier_pairing (cutoffFullCellSymbol z σ)
    (cutoffFullCellSymbol_integrable D hσ0 hσ)]
  change (64 : ℂ) * (carrier (latticeShift a - latticeShift b) *
    ((blochDensity : ℂ) * inner ℂ g
      (angularFourier (cutoffFullCellSymbol z σ) (latticeShift b - latticeShift a) f))) = _
  push_cast
  ring

def resolventCellBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) : CellMap :=
  ((embedLatticeCell a)†).comp ((resolvent D hσ0 hσ).comp (embedLatticeCell b))

theorem resolventCellBlock_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    resolventCellBlock D hσ0 hσ a b =
      (((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b)) •
        angularFourier (cutoffFullCellSymbol z σ) (latticeShift b - latticeShift a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (((embedLatticeCell a)†) (resolvent D hσ0 hσ (embedLatticeCell b f))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, resolvent_fourier_pairing D hσ0 hσ,
    smul_apply, inner_smul_right]

def resolventSpatialBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (cellProjection a).comp ((resolvent D hσ0 hσ).comp (cellProjection b))

theorem resolventSpatialBlock_norm_le_kernel {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤
      64 * ‖angularFourier (cutoffFullCellSymbol z σ) (latticeShift b - latticeShift a)‖ := by
  have hb := spatialBlock_norm_le (resolvent D hσ0 hσ) a b
  change ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ ‖resolventCellBlock D hσ0 hσ a b‖ at hb
  apply hb.trans
  rw [resolventCellBlock_eq, norm_smul, norm_mul, carrier_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [blochDensity_le_one]

theorem resolventSpatialBlock_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ 4 * (h^2)⁻¹ := by
  unfold resolventSpatialBlock
  calc
    _ ≤ ‖cellProjection a‖ * (‖resolvent D hσ0 hσ‖ * ‖cellProjection b‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ((4 * (h^2)⁻¹) * 1) := by
      gcongr
      · exact cellProjection_norm_le a
      · exact resolvent_norm_le D hσ0 hσ
      · exact cellProjection_norm_le b
    _ = _ := by ring

#print axioms resolventCellBlock_eq
#print axioms resolventSpatialBlock_norm_le_kernel

end Maxwell.Continuum.CellGauge
