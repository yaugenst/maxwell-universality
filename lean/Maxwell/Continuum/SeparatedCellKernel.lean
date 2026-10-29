import Maxwell.Continuum.SeparatedCellPairing
import Maxwell.Continuum.CellLatticePhase
import Maxwell.Continuum.OperatorFourierIntegral

/-! The physical separated cell block is exactly the operator Fourier
kernel of the fully gauged symbol, including the Bloch measure and carrier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber Auxiliary Bloch OperatorFourier MeasureTheory Set Metric
open scoped InnerProduct

local instance : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] separatedSymbol cutoffCellSymbol physicalSeparated embedLatticeCell

def blochDensity : ℝ := ((2 * Real.pi)^3)⁻¹

theorem blochDensity_pos : 0 < blochDensity := by unfold blochDensity; positivity

theorem blochDensity_le_one : blochDensity ≤ 1 := by
  unfold blochDensity
  apply (inv_le_one₀ (by positivity : 0 < (2 * Real.pi)^3)).mpr
  have hb : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hb 3

theorem cutoff_zero_outside_quasi {q : Space} (hq : q ∉ quasiCell) : cutoff q = 0 := by
  by_contra hc
  apply hq
  intro j
  have hj := cutoff_ne_zero_coordinate_lt hc j
  have hr : 2 * PeriodicBand.smallRadius < Real.pi / 2 := by
    have hb : 2 * PeriodicBand.smallRadius ≤ 1 := by norm_num [PeriodicBand.smallRadius, backgroundAmplitude]
    linarith [Real.pi_gt_three]
  have hj' := abs_lt.mp (hj.trans hr)
  exact ⟨by linarith [hj'.1], hj'.2⟩

theorem cutoffCellSymbol_zero_outside (z σ : ℝ) {q : Space} (hq : q ∉ quasiCell) :
    cutoffCellSymbol z σ q = 0 := by
  unfold cutoffCellSymbol cutoffSymbol
  rw [cutoff_zero_outside_quasi hq, Complex.ofReal_zero]
  exact zero_smul ℂ (realSymbol (separatedCellSymbol z σ) q)

theorem quasi_integral_supported {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : ∀ q ∉ quasiCell, f q = 0) :
    (∫ q : QuasiCell, f q.val ∂quasiMeasure) = blochDensity • ∫ q, f q := by
  rw [quasiMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 * Real.pi)^3)⁻¹),
    integral_subtype_comap quasiCell_measurable]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hf

theorem cutoffCellSymbol_integrable {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) : Integrable (cutoffCellSymbol z σ) := by
  unfold cutoffCellSymbol
  exact (cutoffSymbol_contDiff (separatedCellSymbol z σ) (separatedCellSymbol_analytic D hσ0 hσ)).continuous
    |>.integrable_of_hasCompactSupport (cutoffSymbol_compact (separatedCellSymbol z σ))

theorem physicalSeparated_fourier_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (physicalSeparated D hσ0 hσ (embedLatticeCell b f)) =
      ((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b) *
        inner ℂ g (angularFourier (cutoffCellSymbol z σ) (latticeShift b - latticeShift a) f) := by
  rw [physicalSeparated_cell_pairing D hσ0 hσ]
  simp_rw [latticePhase_ratio]
  have he : (∫ q : QuasiCell, (carrier (latticeShift a - latticeShift b) *
      Complex.exp ((-inner ℝ q.val (latticeShift b - latticeShift a) : ℝ) * Complex.I)) *
        inner ℂ g (cutoffCellSymbol z σ q.val f) ∂quasiMeasure) =
      carrier (latticeShift a - latticeShift b) *
        ∫ q : QuasiCell, angularPhase q.val (latticeShift b - latticeShift a) *
          inner ℂ g (cutoffCellSymbol z σ q.val f) ∂quasiMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by unfold angularPhase; ring
  have hz (q : Space) (hq : q ∉ quasiCell) :
      angularPhase q (latticeShift b - latticeShift a) * inner ℂ g (cutoffCellSymbol z σ q f) = 0 := by
    rw [cutoffCellSymbol_zero_outside z σ hq, zero_apply, inner_zero_right, mul_zero]
  have hqi := quasi_integral_supported
    (fun q : Space => angularPhase q (latticeShift b - latticeShift a) *
      inner ℂ g (cutoffCellSymbol z σ q f)) hz
  rw [he, hqi, ← angularFourier_pairing (cutoffCellSymbol z σ)
    (cutoffCellSymbol_integrable D hσ0 hσ)]
  change (64 : ℂ) * (carrier (latticeShift a - latticeShift b) *
    ((blochDensity : ℂ) * inner ℂ g
      (angularFourier (cutoffCellSymbol z σ) (latticeShift b - latticeShift a) f))) = _
  push_cast
  ring

def separatedCellBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) : CellMap :=
  ((embedLatticeCell a)†).comp ((physicalSeparated D hσ0 hσ).comp (embedLatticeCell b))

theorem separatedCellBlock_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    separatedCellBlock D hσ0 hσ a b =
      (((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b)) •
        angularFourier (cutoffCellSymbol z σ) (latticeShift b - latticeShift a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (((embedLatticeCell a)†) (physicalSeparated D hσ0 hσ (embedLatticeCell b f))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, physicalSeparated_fourier_pairing D hσ0 hσ,
    smul_apply, inner_smul_right]

theorem separatedCellBlock_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖separatedCellBlock D hσ0 hσ a b‖ ≤ (2 : ℝ)^172 *
      Real.exp (-Real.sqrt (400 * ‖latticeShift b - latticeShift a‖ / (2 : ℝ)^157) / 64) := by
  rw [separatedCellBlock_eq, norm_smul, norm_mul, carrier_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  have hk := cutoffCellSymbol_fourier_decay D hσ0 hσ (latticeShift b - latticeShift a)
  calc
    _ ≤ 64 * (24 * (2 : ℝ)^161 *
        Real.exp (-Real.sqrt (400 * ‖latticeShift b - latticeShift a‖ / (2 : ℝ)^157) / 64)) := by
      exact mul_le_mul (by nlinarith [blochDensity_le_one]) hk (norm_nonneg _) (by norm_num)
    _ ≤ _ := by
      have hc : 64 * (24 * (2 : ℝ)^161) ≤ (2 : ℝ)^172 := by norm_num
      nlinarith [Real.exp_pos (-Real.sqrt (400 * ‖latticeShift b - latticeShift a‖ / (2 : ℝ)^157) / 64)]

#print axioms physicalSeparated_fourier_pairing
#print axioms separatedCellBlock_eq
#print axioms separatedCellBlock_norm_le

end Maxwell.Continuum.CellGauge
